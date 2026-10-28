import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo
import OAI.NumberTheory.PadicHodge.IntegralComparison.BilinearQuotient
import Lean.Elab.Tactic.Omega

/-! # Wedge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Wedge

noncomputable section

/-! Concatenation of the original differential symbols over an
arbitrary commutative base ring, before descending the relations. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

theorem append_update_left {A : Type*} {p q : ℕ} (v : Fin p → A) (w : Fin q → A)
    (i : Fin p) (a : A) :
    Fin.append (Function.update v i a) w =
      Function.update (Fin.append v w) (i.castAdd q) a := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · by_cases h : k = i
    · subst k
      simp
    · have h' : k.castAdd q ≠ i.castAdd q :=
        fun e => h (Fin.ext (congrArg (fun z : Fin (p + q) => z.val) e))
      simp [h, h']
  · have h : Fin.natAdd p k ≠ i.castAdd q := by
      intro e
      have he := congrArg Fin.val e
      change p + k.val = i.val at he
      omega
    simp [h]

theorem append_update_right {A : Type*} {p q : ℕ} (v : Fin p → A) (w : Fin q → A)
    (i : Fin q) (a : A) :
    Fin.append v (Function.update w i a) =
      Function.update (Fin.append v w) (Fin.natAdd p i) a := by
  funext j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · have h : k.castAdd q ≠ Fin.natAdd p i := by
      intro e
      have he := congrArg Fin.val e
      change k.val = p + i.val at he
      omega
    simp [h]
  · by_cases h : k = i
    · subst k
      simp
    · have h' : Fin.natAdd p k ≠ Fin.natAdd p i := by
        intro e
        apply h
        exact Fin.ext (Nat.add_left_cancel (congrArg (fun z : Fin (p + q) => z.val) e))
      simp [h, h']

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def rawWedge (p q : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A p →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Raw A q →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q) :=
  Finsupp.linearCombination A (fun v =>
    Finsupp.linearCombination A (fun w => AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A 1 (Fin.append v w)))

theorem rawWedge_single (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    rawWedge R A p q (Finsupp.single v a) (Finsupp.single w b) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A (a * b) (Fin.append v w) := by
  simp only [rawWedge, Finsupp.linearCombination_single, LinearMap.smul_apply]
  rw [smul_smul, ← AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntegralDeRham.Wedge
