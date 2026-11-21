# CI

Use project.clj and Leiningen across the JVM matrix. Run the complete suite with
`lein test`, and keep the explicit pure namespace lane for focused diagnosis.
The project-package workflow qualifies changes to the release build with a real
überjar, embedded documentation and a launch of its help entry point.
The release workflow separately handles publication.
