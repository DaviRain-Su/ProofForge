import Lake
open Lake DSL

package «my-program» where
  version := v!"0.1.0"

-- P2 落地后改为 git tag，并只链接 ProofForgeSvmSdk。
-- 开发期可 path require monorepo。
require «proofforge» from ".." / ".."

@[default_target]
lean_lib «MyProgram»
