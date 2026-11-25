(require '[clojure.java.io :as io])
(import '[clojure.asm ClassReader ClassVisitor MethodVisitor Opcodes])
(let [[path] *command-line-args*]
  (with-open [input (io/input-stream path)]
    (.accept (ClassReader. input)
             (proxy [ClassVisitor] [Opcodes/ASM6]
               (visitMethod [_access name descriptor _signature _exceptions]
                 (println name descriptor)
                 (proxy [MethodVisitor] [Opcodes/ASM6]
                   (visitMethodInsn [_opcode owner callee desc _interface?]
                     (println "  call" owner callee desc)))))
             0)))
