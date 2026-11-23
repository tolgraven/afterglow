# CI

Use project.clj and Leiningen across the JVM matrix. Run the complete suite with
`lein test`, and keep the explicit pure namespace lane for focused diagnosis.
The project-package workflow qualifies changes to the release build with a real
überjar, embedded documentation and a launch of its help entry point.
The release workflow separately handles publication.

## Pull request evidence

Include a still image and a short GIF or video in every PR description. Use a
running build, a simulator with identified input, or a replay of captured
runtime output. Give the build revision and the actions a reviewer is seeing.
Update both when the demonstrated behavior changes. For a 3D change, capture
the moving scene at a representative camera angle and include the touch layout
when its behavior changes. For a performance change, show the measured workload,
units and missed deadlines alongside the typical result.

Attach the media directly on GitHub or use commit-pinned links to a dedicated
media branch. Open the published still and recording from the PR to confirm
both are readable. Keep binary review captures off the application branch.
