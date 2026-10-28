import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentData
import OAI.Algorithms.SubexponentialSAT.SubexpMainMomentReadback
import OAI.Algorithms.SubexponentialSAT.SubexpMainSystemReadback

namespace OAI.Algorithms

/-! The actual layout output supplies all initialization and CRT constants.
Only the collector's produced node and jet arrays, with their mathematical
interpretation, remain inputs to the final readback constructor. -/

namespace SubexponentialSAT.SubexpMainMomentOutput

noncomputable section

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutSpec
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpQuarticRing SubexpLiftRing

variable {er es p r Δ R D : ℕ} [Fact p.Prime] [NeZero r]
  {hregs : 16 ≤ er} {alloc : Allocation es}
  {a middle layoutOut initialized : MainState er es}
  {hr : 0 < r} {hQ : 0 < p^4 - 1}
  {scopes : List (List ℕ)}
  {hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ}
  {tables : List (List Bool)}
  (h : SubexpMainLayoutExecution.Result hregs alloc a middle layoutOut
    p r Δ R D hr hQ scopes hd tables)

include h in
theorem layout_width :
    (layoutOut.stacks (persistent es 13)).length = baseWidth p (D + 1) :=
  (congrArg List.length (SubexpMainMomentData.layout_target h 1)).trans
    (SubexpPreparedQuarticPrelude.widthWord_length p (D + 1))

include h in
theorem setup_execution :
    ∃ n ≤ SubexpMainNodeSetup.runtimeBound alloc layoutOut D,
      ∃ b : MainState er es,
        Eval (SubexpMainNodeSetup.procedure er alloc).invoke n layoutOut b ∧
        SubexpMainNodeInitialization.Result alloc
          (SubexpMainNodeSetup.prepared alloc layoutOut) b D := by
  apply SubexpMainNodeSetup.execution alloc layoutOut D
  · rw [layout_width h]
    dsimp [baseWidth]
    positivity
  · exact SubexpMainMomentData.layout_dimension h

include h in
theorem layout_persistent (i : Fin 32)
    (hi : i ∉ SubexpMainCacheSetup.changedPersistent) :
    layoutOut.stacks (persistent es i) = a.stacks (persistent es i) :=
  (SubexpMainLayoutRows.Result.persistent_frame (List.ofFn h.choices.coefficients)
    h.choices.packing.packing scopes hd h.rows i hi).trans
    (h.choices.prefixResult.persistent i)

variable (hi : SubexpMainNodeInitialization.Result alloc
  (SubexpMainNodeSetup.prepared alloc layoutOut) initialized D)
  (out : SubexpNodeWideLoop.Data)
  (h5 : out.stacks 5 = (SubexpMainMoments.projected alloc
    (SubexpMainNodeScratch.result alloc initialized)).stacks 5)
  (h10 : out.stacks 10 = (SubexpMainMoments.projected alloc
    (SubexpMainNodeScratch.result alloc initialized)).stacks 10)

local notation "final" => SubexpMainMoments.installed alloc
  (SubexpMainNodeScratch.result alloc initialized) out
local notation "N" => Fintype.card (Fin D)
local notation "target" => SubexpMainMomentData.target p N

variable {k : ℕ} {tau : ℚ} {F : Type*} [Fintype F] [DecidableEq F]
  (S : Factor.System (Fin D) F (ZMod p))
  {c : Parameters p k Δ r tau}
  (L : Layout (E := SubexpActualRing.E p) S.toPattern c)

def readback (crtAlloc : SubexpMainCRT.Allocation es)
    (nodes : Fin c.Q → SubexpCRTSelectedInput.Coefficient p N)
    (jets : Fin c.Q → SubexpCRTSelectedInput.Jet p N)
    (hn : ∀ i, SubexpCRTSelectedInput.decode p N (nodes i) =
      SubexpCRTAtZero.selectedNode S L i)
    (hj : ∀ i, SubexpCRTSelectedInput.denote p N (jets i) =
      SubexpCRTSelectedInput.selectedJet S L i)
    (hnodes : out.stacks 288 =
      (List.finRange c.Q).flatMap (fun i => SubexpFlatAdd.encode (nodes i)))
    (hjets : out.stacks 297 = (List.finRange c.Q).flatMap
      (fun i => SubexpPolynomialPowerProgram.encode p (N + 1) (jets i)))
    (hexponent : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2)
    (hdimension : CounterPrograms.value (a.stacks (persistent es 19)) = D) :
    SubexpMainSystemReadback.Readback S L crtAlloc final := by
  have frame := SubexpMainMomentInvariant.persistent_frame hi out h5 h10
  have hM : layoutOut.stacks (persistent es 12) =
      (SubexpMainMomentData.target p D).modulus.bits :=
    SubexpMainMomentData.layout_target h 0
  have ht : layoutOut.stacks (persistent es 14) =
      SubexpPreparedQuarticSetup.flat (SubexpMainMomentData.target p D).reduction :=
    SubexpMainMomentData.layout_target h 2
  have ho : layoutOut.stacks (persistent es 30) =
      SubexpPreparedQuarticSetup.flat (SubexpMainMomentData.target p D).one :=
    SubexpMainMomentData.layout_target h 4
  have hm : layoutOut.stacks (persistent es 31) =
      (SubexpPreparedQuarticSetup.minusOne p (D + 1)).val :=
    SubexpMainMomentData.layout_target h 5
  rw [SubexpMainRowCache.setup_flat_eq_flat, SubexpMainRowCache.flat_eq_encode] at ht ho
  refine {
    modulus := (target).modulus
    reduction := (target).reduction
    one := (target).one
    minusOne := SubexpPreparedQuarticSetup.minusOne p (N + 1)
    width := layoutOut.stacks (persistent es 13)
    exponent := a.stacks (persistent es 29)
    nodes := nodes
    jets := jets
    width_length := ?_
    reduction_value := (target).reduction_spec
    one_value := (target).one_spec
    minusOne_value := SubexpPreparedQuarticSetup.minusOne_value p (N + 1)
    exponent_value := hexponent
    node_values := hn
    jet_values := hj
    modulus_word := ?_
    width_word := frame 13
    reduction_word := ?_
    exponent_word := (frame 29).trans (layout_persistent h 29 (by decide))
    one_word := ?_
    minusOne_word := ?_
    dimension_word := ?_
    node_words := ?_
    jet_words := ?_ }
  · simpa only [Fintype.card_fin] using layout_width h
  · rw [Fintype.card_fin]
    exact (frame 12).trans hM
  · rw [Fintype.card_fin]
    exact (frame 14).trans ht
  · rw [Fintype.card_fin]
    exact (frame 30).trans ho
  · rw [Fintype.card_fin]
    exact (frame 31).trans hm
  · rw [frame 19, layout_persistent h 19 (by decide)]
    simpa only [Fintype.card_fin] using hdimension
  · exact (SubexpMainMoments.installed_nodes alloc _ out).trans hnodes
  · exact (SubexpMainMoments.installed_jets alloc _ out).trans hjets

end
end SubexponentialSAT.SubexpMainMomentOutput

end OAI.Algorithms
