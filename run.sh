#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
repo=/workspace/worktrees/afterglow-387-keyframe-validation
jars=$(cat "$here/jars.classpath")
base="$repo/src:$repo/test:$repo/dev:$repo/resources:$jars"
run_java() {
  local trial=$1
  shift
  local classpath=$base
  if [[ $trial == A* ]]; then classpath="$here/baseline:$classpath"; fi
  local -a tier=()
  if [[ ${KEYFRAME_JVM_MODE:-default} == c1 ]]; then tier=(-XX:TieredStopAtLevel=1); fi
  java "${tier[@]}" -Djava.awt.headless=true -XX:ActiveProcessorCount=2 -Xms512m -Xmx512m -cp "$classpath" clojure.main "$@"
}
case "${1:?choose measure, replay, or bytecode}" in
  measure)
    for trial in A1 B1 B2 A2; do
      local_trial=${KEYFRAME_TRIAL_PREFIX:-}$trial
      run_java "$trial" "$here/measure.clj" > "$here/$local_trial.edn" 2> "$here/$local_trial.log"
    done
    ;;
  replay)
    for trial in A B; do
      run_java "$trial" "$here/replay.clj" "$here/$trial" > "$here/$trial-replay.log" 2>&1
    done
    cmp "$here/A-trace.csv" "$here/B-trace.csv"
    cmp "$here/A-dmx.bin" "$here/B-dmx.bin"
    cmp "$here/A-native.bin" "$here/B-native.bin"
    ;;
  bytecode)
    for trial in A B; do
      mkdir -p "$here/classes-$trial"
      run_java "$trial" -e "(binding [*compile-path* \"$here/classes-$trial\"] (compile 'afterglow.runtime.keyframes.values))" > "$here/$trial-compile.log" 2>&1
      run_java "$trial" "$here/bytecode.clj" "$here/classes-$trial/afterglow/runtime/keyframes/values\$valid_column_QMARK_.class" > "$here/$trial-bytecode.txt"
    done
    ;;
esac
