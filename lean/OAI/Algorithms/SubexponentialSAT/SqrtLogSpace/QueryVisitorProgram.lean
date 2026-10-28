import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoaderCore
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram

/-! Fixed two-pass visit of one emitted attained-signature tuple. The first
pass reconstructs the entire ambient representative assignment; the second
rescans the assignments in each head against those fixed foreign values.
Every concrete subroutine is fixed here, without an evaluator argument. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram

open BitProgram StructuredCalls
noncomputable section

abbrev Code := Cmd 40 896

/-- Load the head at the reverse traversal's paid unary address. The suspended
DFS address on845 and its representative frames remain caller data. -/
def loadHead : Code := .call (SignatureHeadLoader.programFrom 843)

/-- Install each representative into the ambient tuple before evaluating any
head. This pass also handles zero-width heads by consuming their real frame. -/
def baselineHead : Code :=
  .seq (.call (SignatureHeadLoader.programFrom 843))
    QueryTupleVisitor.installRepresentative

/-- The full key and factor-record stream are staged once per head. All raw
head assignments then pass through the concrete key/correction gate, factor
evaluator, and addition/reset path before multiplication into the tuple. -/
def evaluateLoadedHead : Code :=
  .seq SignatureHeadPrepare.command
    (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command)

def evaluateHead : Code := .seq loadHead evaluateLoadedHead

theorem evaluateLoadedHead_eval {n m : ℕ} {a b c : State 40 896}
    (hp : Eval SignatureHeadPrepare.command n a b)
    (he : Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command) m b c) :
    Eval evaluateLoadedHead (n + m) a c := by
  unfold evaluateLoadedHead
  exact hp.seq he

theorem evaluateHead_eval {n m : ℕ} {a b c : State 40 896}
    (hl : Eval loadHead n a b) (he : Eval evaluateLoadedHead m b c) :
    Eval evaluateHead (n + m) a c := by
  unfold evaluateHead
  exact hl.seq he

theorem evaluateLoadedHead_prefix {n m B : ℕ} {a b c : State 40 896}
    (hp : Eval SignatureHeadPrepare.command n a b)
    (he : Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command) m b c)
    (hpp : QueryExecution.PrefixBound SignatureHeadPrepare.command n a B)
    (hep : QueryExecution.PrefixBound
      (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) m b B) :
    QueryExecution.PrefixBound evaluateLoadedHead (n + m) a B := by
  unfold evaluateLoadedHead
  exact QueryExecution.prefix_seq hp he hpp hep

theorem evaluateHead_prefix {n m B : ℕ} {a b c : State 40 896}
    (hl : Eval loadHead n a b) (he : Eval evaluateLoadedHead m b c)
    (hlp : QueryExecution.PrefixBound loadHead n a B)
    (hep : QueryExecution.PrefixBound evaluateLoadedHead m b B) :
    QueryExecution.PrefixBound evaluateHead (n + m) a B := by
  unfold evaluateHead
  exact QueryExecution.prefix_seq hl he hlp hep

/-- One fixed visitor reconstructs representatives, evaluates all head sums,
and adds the completed product to the current finite-difference pair. The
unit construction and empty passes retain the empty-tuple contribution. -/
def visitor : Code :=
  .seq QueryTupleInit.command
    (.seq (QueryExecution.replay baselineHead)
      (.seq (QueryExecution.replay evaluateHead) QueryExecution.TupleEnd.command))

def program := compiled visitor 837 851

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
