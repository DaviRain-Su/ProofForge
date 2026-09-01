import Lake
open Lake DSL

package «my-program» where
  version := v!"0.1.0"

/-- Path require for monorepo/`pf init` (rewritten to `..` by init).
For a published release, replace with:
  require «proofforge» from git
    "https://github.com/DaviRain-Su/ProofForge.git" @ "v0.0.1"
and keep imports on `ProofForge.Attr` + `ProofForge.Svm.Sdk` only. -/
require «proofforge» from ".." / ".."

@[default_target]
lean_lib «MyProgram»
