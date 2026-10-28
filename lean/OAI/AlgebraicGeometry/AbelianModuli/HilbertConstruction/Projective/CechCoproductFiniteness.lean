import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCech
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.FunctorFiniteCoproducts

/-! # Cech Coproduct Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCoproductFiniteness

noncomputable section

/-! Actual projective Čech homology preserves finite generation under finite sums of sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCech_homology_finite_coproduct {ι : Type u} [Finite ι]
    (M : ι → (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules) (q : ℕ)
    (hM : ∀ i, Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (M i)).homology q)) :
    Module.Finite R (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (∐ M)).homology q) := by
  let F : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules ⥤ ModuleCat.{u} R :=
    CoefficientCechFunctor.projectiveCoefficientCechFunctor I ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q
  have : F.Additive := by dsimp [F]; infer_instance
  exact HilbertConstruction.Additive.FunctorFiniteCoproducts.additive_functor_finite_coproduct F M hM

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechCoproductFiniteness
