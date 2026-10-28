import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPadded
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntrySemantics

namespace OAI.Algorithms

/-! The physical entry dispatch does not need a head-color oracle. The actual
head-ID scan supplies the column-head invariant; the joint guard compares the
two decoded type words at the requested node. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

def localEntry (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (v w : I) : ℤ :=
  match P.lookup v with
  | none => if w = v then 1 else 0
  | some (j,u) => match P.lookup w with
    | none => 0
    | some (k,y) =>
      if j = k ∧ anchorValid (0 : Fin 1) t u y then
        (if u = y then (2 : ℤ)^(R-1) else 0) -
          LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u y
      else 0

omit [Fintype I] in
theorem lookup_label (P : PackingData I (UniversalType r Q 1))
    (w : I) (k : Fin P.blockCount) (y : UniversalType r Q 1)
    (hw : P.lookup w = some (k,y)) : P.label w = y := by
  rw [← P.lookup_sound w (k,y) hw,P.label_at]

omit [Fintype I] in
theorem localEntry_eq (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v w : I)
    (hwhead : (P.label w).head t = g) :
    localEntry P A R t v w = paddedEntry P A R t g v w := by
  cases hv : P.lookup v with
  | none =>
    by_cases he : w = v
    · subst w
      simp [localEntry,paddedEntry,hv,hwhead]
    · simp [localEntry,paddedEntry,hv,he]
  | some z =>
    rcases z with ⟨j,u⟩
    cases hw : P.lookup w with
    | none => simp [localEntry,paddedEntry,hv,hw]
    | some z =>
      rcases z with ⟨k,y⟩
      have hy : y.head t = g := by
        rw [← lookup_label P w k y hw]
        exact hwhead
      have ha : anchorValid (0 : Fin 1) t u y ↔
          u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) := by
        rw [anchorValid_iff_joint,hy]
      simp [localEntry,paddedEntry,hv,hw,ha,and_assoc]

omit [Fintype I] in
/-- Every incidence in an original-variable fiber has the same head, including
copies that are not covered by a complete block. -/
theorem localEntry_fiber_eq {V : Type*}
    (P : PackingData I (UniversalType r Q 1)) (owner : I → V)
    (head : Fin Q → V → Fin r)
    (hhead : ∀ i t, (P.label i).head t = head t (owner i))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v w : I) (x : V)
    (hx : head t x = g) (hw : owner w = x) :
    localEntry P A R t v w = paddedEntry P A R t g v w := by
  apply localEntry_eq
  rw [hhead,hw,hx]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
