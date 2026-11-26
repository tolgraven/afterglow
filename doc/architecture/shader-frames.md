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

- `:source` is a GLSL 3.30 fragment body. It may start with its own `#version` line (after blank lines only), which is replaced. Any other version line is refused. Author `#extension` lines are moved ahead of the generated declarations, as GLSL requires.
- Afterglow declares the following, so the source must not declare them again:
  - every uniform in `:uniforms`, in name order;
  - `u_resolution` (vec2, the viewport size in pixels);
  - `u_origin` (vec2, the viewport's lower-left corner in window pixels);
  - `out vec4 fragColor`.
- `#line 1` precedes the body, and every line taken out of it (an author version line, the blank lines before it, an `#extension`) stays as an empty line. Driver log line numbers therefore equal the author's line numbers.
- Only the desktop dialect is compiled and tested. `fragment-source` can also emit a `:glsl-es-300` header that declares the same interface, but GLSL ES 3.00 is stricter (for example, it has no implicit int to float conversion), so the same body is not guaranteed to compile in WebGL2.
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

- **One worker.** A renderer owns one desktop GL 3.3 core context and one worker thread, which makes every draw and readback. Teardown runs once on the `afterglow-gpu-cleanup` thread after the worker has stopped, so GL calls still come from one thread at a time. Callers get Futures, and the queue is bounded (8 waiting jobs by default). A full queue throws `::busy` immediately.
- **Owned frames, no direct memory.** The driver reads each frame straight into a fresh heap byte array, and the rows are flipped in place. No direct readback buffer is kept per render target, so memory is the frame arrays themselves: 35 MB for one 4096 × 2160 frame. A host that keeps many large frames must budget for them.
- **Bounded caches.** Programs (16) and render targets (8) are LRU caches. Programs are keyed by the shader map, whose hash is cached, so a render validates the shader once and never rebuilds its source. The source is assembled only when a program compiles. `release!` frees a program early. Status counts `:evictions` (programs) and `:target-evictions`.
- **A failed compile.** `::afterglow.render.gpu.native-context/invalid-program` comes back with `:stage` (`:compile` or `:link`) and the driver `:log`. It leaves every resident program usable, so a host can keep rendering its last working version.
- **Fatal errors.** Any other GL error, or a fence that misses its timeout (1000 ms by default), closes the context. A later call then fails with `::closed`, and the host opens a new renderer.
- **Closing.** `close!` cancels waiting work, lets the active call finish, then releases programs, targets and the context.

## Timing fields

- `:draw-ms` runs from the first GL call to the signalled fence, so it bounds GPU execution for that frame.
- `:readback-ms` covers `glReadPixels` (BGRA, `GL_UNSIGNED_INT_8_8_8_8_REV`) and the row flip.
- `:gpu-ms` is the driver's `GL_TIME_ELAPSED` query. Apple's GL 4.1-over-Metal driver on an M4 Pro returned negative values, so `:gpu-ms` is nil whenever the driver's value is not positive.

These are the medians of 200, 200, 100, 60 and 30 frames of a trivial gradient on that machine, with other agents loading it:

| Target | Draw (ms) | Readback (ms) | Total per frame (ms) |
| --- | ---: | ---: | ---: |
| 200 × 1 | 0.28 | 0.07 | 0.55 |
| 640 × 360 | 0.34 | 0.58 | 1.11 |
| 1280 × 720 | 0.25 | 0.80 | 1.15 |
| 1920 × 1080 | 0.63 | 1.79 | 2.49 |
| 4096 × 2160 | 1.15 | 4.62 | 5.93 |

Tolglow's `tolglow.bench-shader-cues` measures whole shows with up to eight cues ([results](https://github.com/tolgraven/tolglow/blob/master/docs/shader-cues.md#measurements)).

## Tests

- `lein test afterglow.render.shader-frames-test` covers validation, assembly (including line numbering and `#extension` placement), packing, viewports and the row flip. It is part of `lein test-pure`.
- `lein with-profile +native-gpu test afterglow.render.gpu-shader-frames-test` renders on the real driver. It covers:
  - top-down BGRA with uniforms;
  - log line numbers after an author version line, blank lines and an `#extension`;
  - a 200-pixel row addressed pixel for pixel;
  - viewport clearing and coordinates;
  - a failed compile that keeps the resident program;
  - owned arrays and bounded caches;
  - close.

The native-GPU workflow (`.github/workflows/native-moving-head-gpu.yml`) runs it under `xvfb-run -a` with Mesa. Software GL establishes correctness only.
