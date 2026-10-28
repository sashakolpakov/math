import OAI.RepresentationTheory.Theta.Geometric.SquareZero.AffineFactorization
import OAI.RepresentationTheory.Theta.Geometric.SquareZero.Reduction
import OAI.RepresentationTheory.Theta.Geometric.OpenRegularFunctionValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts

/-! # Scheme Factorization -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeFactorization

noncomputable section

/-! Every native scheme parameter constant modulo a square-zero ideal
factors through the actual constants-plus-ideal split test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

attribute [local instance] SquareZero.Ideal.idealCoefficientOppositeModule SquareZero.Ideal.idealCoefficientCentralScalar

set_option backward.isDefEq.respectTransparency false in
theorem squareZero_schemeTest_factorization
    {R : Type} [CommRing R] [Algebra ℂ R] [Nontrivial R]
    (I : Ideal R) (hI : I * I = ⊥) (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
    (r : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ X) (e : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (h : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I) ≫ r =
      toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I)) ≫ e) :
    ∃ a : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (TrivSqZeroExt ℂ I) ⟶ X,
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ (TrivSqZeroExt ℂ I) R (SquareZero.Ideal.squareZeroIdealMap I hI) ≫ a = r := by
  let t : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := (⊥ : PrimeSpectrum ℂ)
  obtain ⟨U, hU, heU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show e.left t ∈ (⊤ : X.left.Opens) by trivial)
  let j := OpenRegularFunctionValues.regularOpenInclusion X U
  have : IsAffine (OpenRegularFunctionValues.regularOpenScheme X U).left := hU
  have hRe : Set.range e.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    have hz : e.left z ∈ U := (congrArg e.left (Subsingleton.elim t z)) ▸ heU
    exact ⟨⟨e.left z, hz⟩, rfl⟩
  let red := AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R (R ⧸ I) (Ideal.Quotient.mkₐ ℂ I)
  have : Surjective red.left := Reduction.squareZeroIdeal_reduction_surjective I hI
  have hRr : Set.range r.left ⊆ Set.range j.left :=
    (Reduction.scheme_range_subset_of_surjective_reduction red.left r.left
      (toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I))).left e.left (congrArg Over.Hom.left h)).trans hRe
  let r' := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift j r hRr
  let e' := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift j e hRe
  have hr' : r' ≫ j = r := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift_fac j r hRr
  have he' : e' ≫ j = e := AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Lifts.overOpenLift_fac j e hRe
  have hred : red ≫ r' = toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I)) ≫ e' := by
    apply Over.OverMorphism.ext
    apply (cancel_mono j.left).mp
    have H : (red ≫ r') ≫ j = (toUnit (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (R ⧸ I)) ≫ e') ≫ j := by
      rw [Category.assoc, Category.assoc, hr', he']
      exact h
    exact congrArg Over.Hom.left H
  obtain ⟨a, ha⟩ := AffineFactorization.squareZero_affineTest_factorization I hI (OpenRegularFunctionValues.regularOpenScheme X U) r' e' hred
  refine ⟨a ≫ j, ?_⟩
  rw [← Category.assoc, ha, hr']

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.SchemeFactorization
