import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentOutput
import OAI.Algorithms.SubexponentialSAT.SubexpMainCanonicalJetReadback
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutSemantics
import OAI.Algorithms.SubexponentialSAT.SubexpNodeIndexSemantics

namespace OAI.Algorithms

/-! Readback of the canonical arrays emitted by the actual node collector.
The typed node and jet families are constructed here, rather than supplied
as independent witnesses. The collector's restored workspace gives both
persistent arithmetic-input frames. -/

namespace SubexponentialSAT.SubexpMainMomentCanonicalOutput

noncomputable section

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutSpec
open SubexpLayoutPorts (Allocation)
open SubexpMainMomentData (store)

variable {er es p k r Δ D : ℕ} {tau : ℚ} [Fact p.Prime] [NeZero r]
  {hregs : 16 ≤ er} {alloc : Allocation es}
  {a middle layoutOut initialized : MainState er es}
  {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (c : Parameters p k Δ r tau) (h4 : c.h = 4)
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ c.R D hr hQ scopes hd tables)
  (hi : SubexpMainNodeInitialization.Result alloc
    (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (out : SubexpNodeWideLoop.Data)
  (ready : SubexpNodeWideLoop.Ready (SubexpNodeWorkspace.Ready (store alloc initialized)) out)

include ready in
theorem modulus_frame : out.stacks 5 =
    (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks 5 :=
  SubexpNodeWorkspace.ready_master ready.ok 5 (by decide)

include ready in
theorem width_frame : out.stacks 10 =
    (SubexpMainMoments.projected alloc (SubexpMainNodeScratch.result alloc initialized)).stacks 10 :=
  SubexpNodeWorkspace.ready_master ready.ok 10 (by decide)

include hi ready in
theorem persistent_frame (i : Fin 32) :
    (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out).stacks
        (persistent es i) = layoutOut.stacks (persistent es i) :=
  SubexpMainMomentInvariant.persistent_frame hi out
    (modulus_frame out ready) (width_frame out ready) i

variable {F : Type*} [Fintype F] [DecidableEq F]
  (S : Factor.System (Fin D) F (ZMod p))
  (L : Layout (E := SubexpActualRing.E p) S.toPattern (SubexpMainLayoutSemantics.parameters c h4))

def readback (crtAlloc : SubexpMainCRT.Allocation es)
    (hnode : ∀ i, L.node i = (SubexpMachineNodeOrder.nodeEquiv p i).val)
    (hnodes : out.stacks 288 =
      (List.ofFn (SubexpNodeIndexSemantics.thetaWord p D)).flatten)
    (hjets : out.stacks 297 =
      (List.ofFn (SubexpNodeCanonicalJet.canonicalJetBytes L
        (SubexpMainCanonicalJetReadback.table S))).flatten)
    (hexponent : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2)
    (hdimension : CounterPrograms.value (a.stacks (persistent es 19)) = D) :
    SubexpMainSystemReadback.Readback S L crtAlloc
      (SubexpMainMoments.installed alloc (SubexpMainNodeScratch.result alloc initialized) out) := by
  apply SubexpMainMomentOutput.readback h hi out
    (modulus_frame out ready) (width_frame out ready) S L crtAlloc
    (SubexpMainMomentReadback.nodeCode p (Fintype.card (Fin D)))
    (SubexpMainCanonicalJetReadback.selectedCode S L)
  · intro i
    exact SubexpMainMomentReadback.nodeCode_selected S L i i (hnode i)
  · exact SubexpMainCanonicalJetReadback.selectedCode_decode S L
  · have hn := hnodes.trans (SubexpMainMomentReadback.node_words p D)
    apply hn.trans
    exact congrArg (fun d => (List.finRange (p^4 - 1)).flatMap fun i =>
      SubexpFlatAdd.encode (SubexpMainMomentReadback.nodeCode p d i))
      (Fintype.card_fin D).symm
  · exact hjets.trans (SubexpMainCanonicalJetReadback.selectedCode_words S L)
  · exact hexponent
  · exact hdimension

end
end SubexponentialSAT.SubexpMainMomentCanonicalOutput

end OAI.Algorithms
