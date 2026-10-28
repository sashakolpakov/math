import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! # Wedge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Wedge

noncomputable section

/-! Wedge products on the original differential-symbol modules over a
rational algebra, defined through their canonical exterior-form
equivalence and normalized on the original symbols. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

def exteriorMul (p q : ℕ) :
    (⋀[A]^p Ω[A⁄R]) →ₗ[A] (⋀[A]^q Ω[A⁄R]) →ₗ[A] (⋀[A]^(p + q) Ω[A⁄R]) :=
  DirectSum.gMulLHom A (fun n => ⋀[A]^n Ω[A⁄R])

def wedge (p q : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q →ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A (p + q) :=
  (((exteriorMul R A p q).compr₂ (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A (p + q)).symm.toLinearMap).comp
    (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A p).toLinearMap).compl₂ (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A q).toLinearMap

theorem toExterior_wedge (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A (p + q) (wedge R A p q x y) =
      exteriorMul R A p q (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A p x) (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A q y) :=
  (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A (p + q)).apply_symm_apply _

theorem toExterior_wedge_coe (p q : ℕ) (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A p) (y : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A q) :
    (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A (p + q) (wedge R A p q x y) : ExteriorAlgebra A Ω[A⁄R]) =
      (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A p x : ExteriorAlgebra A Ω[A⁄R]) *
        (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A q y : ExteriorAlgebra A Ω[A⁄R]) :=
  congrArg Subtype.val (toExterior_wedge R A p q x y)

theorem wedge_symbol (p q : ℕ) (a b : A) (v : Fin p → A) (w : Fin q → A) :
    wedge R A p q (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A b w) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A (a * b) (Fin.append v w) := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv R A (p + q)).injective
  apply Subtype.val_injective
  rw [toExterior_wedge_coe]
  simp only [AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.formsEquiv_symbol, Submodule.coe_smul, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.exteriorSymbol,
    exteriorPower.ιMulti_apply_coe]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 2
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

def degreeCast {m n : ℕ} (h : m = n) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A m ≃ₗ[A] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n := by
  subst n
  exact LinearEquiv.refl _ _

omit [Algebra ℚ A] in
theorem degreeCast_symbol {m n : ℕ} (h : m = n) (a : A) (v : Fin m → A) :
    degreeCast R A h (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (fun i => v (Fin.cast h.symm i)) := by
  subst n
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RationalDeRham.Wedge
