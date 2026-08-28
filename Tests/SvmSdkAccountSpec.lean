import Examples.AccountView
import Examples.Trio
import ProofForge

/-!
Focused SVM SDK account-facade gates. `Examples.Trio` consumes fixed Account/Signer handles;
`Examples.AccountView` independently consumes a bounded dynamic window. Existing extraction,
assembly, and Mollusk specs own runtime behavior; these gates pin descriptor erasure and prove no
new operation or IR vocabulary is needed.
-/

namespace Tests.SvmSdkAccountSpec

open ProofForge.Svm.Sdk

private def state := Examples.Trio.init 0

#guard Examples.Trio.account0 == Account.Handle.at 0
#guard Examples.Trio.account2 == Account.Handle.at 2
#guard Examples.Trio.signer1 == Signer.Handle.at 1

#guard Examples.Trio.lamports2 state == ProofForge.Svm.Runtime.accLamports 2
#guard Examples.Trio.dataLen2 state == ProofForge.Svm.Runtime.accDataLen 2
#guard Examples.Trio.signer2 state == ProofForge.Svm.Runtime.isSigner 2
#guard Examples.Trio.writable2 state == ProofForge.Svm.Runtime.isWritable 2
#guard Examples.Trio.executable2 state == ProofForge.Svm.Runtime.isExecutable 2
#guard Examples.Trio.key20 state == ProofForge.Svm.Runtime.accKeyWord 2 0
#guard Examples.Trio.needSig1 state == ProofForge.Svm.Runtime.signerKey 1
#guard Examples.Trio.self0 state == ProofForge.Svm.Runtime.ownerIsSelf 0
#guard Examples.Trio.self2 state == ProofForge.Svm.Runtime.ownerIsSelf 2

#guard Examples.AccountView.window == Account.View.bounded 1 4
#guard Examples.AccountView.window.wellFormed
#guard Examples.AccountView.window.peekData 0 0 == 0
#guard Examples.AccountView.window.peekKey 3 1 == 0
#guard Examples.AccountView.window.peekSigner 2 == 0
#guard Examples.AccountView.window.ownedBySelf 0 == 0

end Tests.SvmSdkAccountSpec
