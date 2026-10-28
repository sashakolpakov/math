import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramProducedRankJoin
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPackLabels

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

abbrev packing (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    PackingData (Fin p.incidences) (UniversalType p.r p.Q 1) :=
  (Problem.spec_dimension p a tail) ▸ (p.spec a tail).suffix.packing

abbrev owner (p : Problem) :=
  PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le
abbrev factor (p : Problem) :=
  PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le

def words (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (Fin p.n ⊕ Fin p.factors) → Word p.r p.Q
  | .inl v => (p.words a tail).get ⟨v.val,by rw [p.words_length]; omega⟩
  | .inr f => (p.words a tail).get ⟨p.n+f.val,by rw [p.words_length]; omega⟩

def rows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :=
  (p.words a tail).map SubexponentialSAT.Subexp.ReadPlan.encodeWord

theorem packing_label (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    (packing p a tail).label=Packing.incidenceType (owner p) (factor p) (words p a tail) := by
  rfl

theorem packing_head (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (i : Fin p.incidences) (t : Fin p.Q) :
    ((packing p a tail).label i).head t=words p a tail (.inl (owner p i)) t := rfl

/-- Native row bytes, including factor rows after all ambient head rows. -/
theorem rows_eq_spec (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q)) :
    rows p a tail=(p.spec a tail).params.rows := rfl

theorem head_row (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (v : Fin p.n) :
    (rows p a tail).getD v.val []=SubexponentialSAT.Subexp.ReadPlan.encodeWord (words p a tail (.inl v)) := by
  have hv : v.val < (p.words a tail).length := by rw [p.words_length]; omega
  unfold rows
  rw [List.getD_eq_getElem _ _ (by simpa using hv),List.getElem_map]
  rfl

theorem selected_head (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (low : List Bool) (t : Fin p.Q) (g : Fin p.r) (v : Fin p.n)
    (hv : v.val∈LeafHeadSetupProgram.selectedHeads p.n (rows p a tail) low (t.val*p.r+g.val)) :
    words p a tail (.inl v) t=g := by
  have hpred : HeadIdentifierProgram.predicate (rows p a tail) low (t.val*p.r+g.val) v.val=true :=
    (List.mem_filter.mp hv).2
  unfold HeadIdentifierProgram.predicate at hpred
  rw [head_row,HeadIdentifierProgram.encodeWord_getD] at hpred
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp hpred).2

/-- Distinct nonzero rational nodes suffice for this integer rank proof.
They are proof data and cause no change to the executed finite-ring code. -/
def rationalNode (Q : ℕ) (i : Fin Q) : ℚ := (i.val:ℚ)+1

def rationalUnits (Q : ℕ) : SubexponentialSAT.SubexpRowInterpolation.NodeUnits (rationalNode Q) :=
  SubexponentialSAT.SubexpRowInterpolation.NodeUnits.ofField _
    (by intro i j h; apply Fin.ext; exact_mod_cast (by simpa [rationalNode] using h : (i.val:ℚ)=(j.val:ℚ)))
    (by
      intro i
      have hi : (0:ℚ) ≤ (i.val:ℚ) := by positivity
      dsimp [rationalNode]
      linarith)

def rationalDenominator (R : ℕ) : ℚˣ :=
  Units.mk0 (LayoutNumerator.denominator R : ℚ) (by
    simp only [LayoutNumerator.denominator]
    positivity)

@[simp] theorem rationalDenominator_val (R : ℕ) :
    (rationalDenominator R : ℚ)=(LayoutNumerator.denominator R : ℚ) := rfl

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
