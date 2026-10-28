import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithmEntry
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeEnumeration

namespace OAI.Algorithms

/-! Executable scalar specifications in the physical side/joint list order.
These definitions do not assert a primitive runtime bound: their exact
identification lets the separately traced scan/arithmetic producer feed the
semantic layout without an arbitrary finite-type ordering oracle. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ}

def headEntry (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u : Joint t g (0 : Fin 1)) (y : LayoutUniversal.Head t g) : ℤ :=
  if y.val ∈ joint t g (0 : Fin 1) then
    (if u.val = y.val then (2 : ℤ) ^ (R-1) else 0) -
      LayoutCoefficientAlgorithm.scalarEntry (0 : Fin 1) t A R u.val y.val
  else 0

theorem headEntry_eq (A R : ℕ) (t : Fin Q) (g : Fin r)
    (u : Joint t g (0 : Fin 1)) (y : LayoutUniversal.Head t g) :
    headEntry A R t g u y = LayoutUniversal.constraints A R t g u y := by
  classical
  have inj : Function.Injective (LayoutUniversal.jointOwner t g) := by
    intro a b h
    exact Subtype.ext (congrArg (fun z => z.val) h)
  by_cases hy : y.val ∈ joint t g (0 : Fin 1)
  · let yy : Joint t g (0 : Fin 1) := ⟨y.val,hy⟩
    have he : LayoutUniversal.jointOwner t g yy = y := Subtype.ext rfl
    change headEntry A R t g u y =
      row (LayoutUniversal.jointOwner t g)
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) u) y
    rw [← he, row_apply_injective _ inj]
    simp only [headEntry, he, ite_eq_left hy, clearedDefect]
    rw [LayoutCoefficientAlgorithm.scalarEntry_eq_entry]
    have heq : u = yy ↔ u.val = y.val := Subtype.ext_iff
    simp only [heq, LayoutNumerator.denominator, LayoutNumerator.joint]
    rfl
  · have hout : y ∉ Set.range (LayoutUniversal.jointOwner t g) := by
      rintro ⟨z,hz⟩
      apply hy
      have hh : z.val = y.val := congrArg Subtype.val hz
      exact hh ▸ z.property
    change headEntry A R t g u y =
      row (LayoutUniversal.jointOwner t g)
        (clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) u) y
    rw [row_eq_zero _ _ _ hout]
    simp [headEntry, hy]

/-- This is only the mathematical name for the actual byte enumeration order;
no invocation of `Fintype.equivFin` enters the matrix producer. -/
noncomputable def orderedHeadMatrix (A R : ℕ) (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) : List (List ℤ) :=
  (SubexponentialSAT.Subexp.TypeEnumeration.jointList hr hQ t g (0 : Fin 1)).map fun u =>
    (SubexponentialSAT.Subexp.TypeEnumeration.sideList hr hQ t g).map fun y =>
      headEntry A R t g u y

theorem orderedHeadMatrix_eq (A R : ℕ) (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) :
    orderedHeadMatrix A R hr hQ t g =
      (SubexponentialSAT.Subexp.TypeEnumeration.jointList hr hQ t g (0 : Fin 1)).map (fun u =>
        (SubexponentialSAT.Subexp.TypeEnumeration.sideList hr hQ t g).map
          (LayoutUniversal.constraints A R t g u)) := by
  simp only [orderedHeadMatrix, headEntry_eq]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
