# Fragment-shader video frames on a JVM GPU context

`afterglow.render.gpu.shader-frames` renders a GLSL fragment shader into an offscreen framebuffer and reads it back as owned BGRA8 pixels. Tolglow's shader cues use it to produce video feeds for strips and projectors at their own frame rate ([tolgraven/tolglow#673](https://github.com/tolgraven/tolglow/issues/673)). The pure half, `afterglow.render.shader-frames`, validates shaders, packs typed uniforms and assembles the GLSL without a GPU.

```clojure
(require '[afterglow.render.gpu.shader-frames :as frames])

(def plasma {:source "void main() {
                        vec2 uv = (gl_FragCoord.xy - u_origin) / u_resolution;
                        fragColor = vec4(uv, u_blue, 1.0);
                      }"
             :uniforms {"u_blue" :float}})

(with-open [r (frames/open!)]
  (frames/await! (frames/compile! r plasma))             ; {:compiled? true} or ex-info with :log
  (frames/await! (frames/render! r plasma {:width 640 :height 360 :uniforms {"u_blue" 0.5}})))
;; => {:pixels <owned top-down BGRA8 byte[]> :width 640 :height 360 :draw-ms … :readback-ms … :gpu-ms …}
```

Run it with `lein with-profile +native-gpu …`, which supplies JOGL.

## Shader contract

- `:source` is a GLSL ES 3.00 fragment body. It may start with its own `#version` line, which is replaced. A second version line is refused.
- Afterglow declares the following, so the source must not declare them again:
  - every uniform in `:uniforms`, in name order;
  - `u_resolution` (vec2, the viewport size in pixels);
  - `u_origin` (vec2, the viewport's lower-left corner in window pixels);
  - `out vec4 fragColor`.
- `#line 1` precedes the body, so driver log line numbers count from the author's first line.
- `fragment-source` emits the same body for `:glsl-330` (this context) and `:glsl-es-300` (WebGL2).
- Uniform types are `:float`, `:int`, `:bool`, `:vec2`, `:vec3` and `:vec4`. `pack-uniforms` refuses:
  - a missing value or an undeclared name;
  - a wrong arity;
  - a value that is not finite or does not fit a float32;
  - an `:int` that is not integral;
  - a `:bool` other than true, false, 0 or 1.
- Limits:
  - source: 65,536 characters;
  - uniforms: 32;
  - target: sides of 1–4096 pixels, 4096 × 2160 pixels in all.
- A `:viewport [x y w h]` is in top-down pixels inside the target. The rest of the target is cleared to opaque black.
- `fragColor` holds display (sRGB) values. The framebuffer is RGBA8 without sRGB conversion, so the bytes match what a video source would deliver.

## Ownership and failure

- **One worker.** A renderer owns one desktop GL 3.3 core context and one worker thread. Every GL object and the direct readback buffer stay on that thread. Callers get Futures, and the queue is bounded (8 waiting jobs by default). A full queue throws `::busy` immediately.
- **Owned frames.** Each frame is copied into a fresh top-down byte array. The worker never hands out or reuses a returned array.
- **Bounded caches.** Programs (16) and render targets (8) are LRU caches keyed by assembled source and by size. `release!` frees a program early.
- **A failed compile.** `::afterglow.render.gpu.native-context/invalid-program` comes back with `:stage` (`:compile` or `:link`) and the driver `:log`. It leaves every resident program usable, so a host can keep rendering its last working version.
- **Fatal errors.** Any other GL error, or a fence that misses its timeout (1000 ms by default), closes the context. A later call then fails with `::closed`, and the host opens a new renderer.
- **Closing.** `close!` cancels waiting work, lets the active call finish, then releases programs, targets and the context.

## Timing fields

- `:draw-ms` runs from the first GL call to the signalled fence, so it bounds GPU execution for that frame.
- `:readback-ms` covers `glReadPixels` (BGRA, `GL_UNSIGNED_INT_8_8_8_8_REV`) and the row flip.
- `:gpu-ms` is the driver's `GL_TIME_ELAPSED` query. Apple's GL 4.1-over-Metal driver on an M4 Pro returned negative values, so `:gpu-ms` is nil whenever the driver's value is not positive.

These are the medians of 200, 200, 100 and 60 frames of a trivial gradient on that machine, with other agents loading it:

| Target | Draw (ms) | Readback (ms) | Total per frame (ms) |
| --- | ---: | ---: | ---: |
| 200 × 1 | 0.18 | 0.04 | 0.35 |
| 640 × 360 | 0.18 | 0.24 | 0.51 |
| 1280 × 720 | 0.24 | 0.86 | 1.18 |
| 1920 × 1080 | 0.63 | 2.05 | 2.81 |

Tolglow's `tolglow.bench-shader-cues` measures whole shows with up to eight cues ([results](https://github.com/tolgraven/tolglow/blob/master/docs/shader-cues.md#measurements)).

## Tests

- `lein test afterglow.render.shader-frames-test` covers validation, assembly, packing, viewports and the row flip. It is part of `lein test-pure`.
- `lein with-profile +native-gpu test afterglow.render.gpu-shader-frames-test` renders on the real driver. It covers:
  - top-down BGRA with uniforms;
  - a 200-pixel row addressed pixel for pixel;
  - viewport clearing and coordinates;
  - a failed compile that keeps the resident program;
  - owned arrays and bounded caches;
  - close.

On headless Linux, use `xvfb-run -a` with Mesa. Software GL establishes correctness only.
