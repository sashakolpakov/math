import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.SpaceSmooth

/-! # Relative Dimension -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RelativeDimension

noncomputable section

/-! The usual projective coordinate charts have the expected smooth
relative dimension over an arbitrary coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false

universe u v

variable (R : Type u) [CommRing R] (τ : Type v) [Finite τ]

def polynomialPresentation :
    Algebra.SubmersivePresentation R (MvPolynomial τ R) τ Empty where
  toGenerators := Algebra.Generators.mvPolynomial R τ
  relation := Empty.elim
  span_range_relation_eq_ker := by simp [Algebra.Generators.ker_mvPolynomial]
  map := Empty.elim
  map_inj := by intro x; exact x.elim
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

theorem polynomial_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card τ) R (MvPolynomial τ R) :=
  (polynomialPresentation R τ).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

variable {R} {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem chart_standardSmooth (i : σ) :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (Away (homogeneousSubmodule σ R) (MvPolynomial.X i)) := by
  classical
  have hc : Nat.card {j : σ // j ≠ i} = Fintype.card σ - 1 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  let : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card σ - 1) R
      (MvPolynomial {j : σ // j ≠ i} R) :=
    hc ▸ polynomial_standardSmooth R {j : σ // j ≠ i}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv
    (Fintype.card σ - 1) (SpaceSmooth.chartEquiv (R := R) i).symm

theorem smooth : SmoothOfRelativeDimension (Fintype.card σ - 1)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
    (P := @SmoothOfRelativeDimension (Fintype.card σ - 1)) _
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.iSup_coordinateOpen_eq_top (R := R) (σ := σ))]
  intro i
  let e := Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (MvPolynomial.X i)
    (AlgebraicGeometry.SheafCohomology.Projective.SpaceChart.MvPolynomial.X_mem_homogeneousSubmodule_one R i) one_pos
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension (Fintype.card σ - 1)) e.inv]
  change SmoothOfRelativeDimension (Fintype.card σ - 1)
    (e.inv ≫ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)
  rw [AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ, ← Category.assoc, ← Category.assoc, ← Proj.awayι,
    Proj.awayι_toSpecZero, ← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension (Fintype.card σ - 1))).mpr
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (Fintype.card σ - 1)).mpr
    (chart_standardSmooth i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.RelativeDimension
