import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationSaturationMembership
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedSaturationNeighborhood
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FiniteEquationCoordinates

/-! # Localization Family Equality Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationFamilyEqualityNeighborhood.GradedHilbert

noncomputable section

/-! Equality of native projective families after any coefficient localization
already holds after inverting one element of its multiplicative set. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u v w
variable {A : Type u} [CommRing A] {n : ℕ}

theorem generated_projectiveSaturation_equality_localization_neighborhood
    (U : Submonoid A) (T : Type u) [CommRing T] [Algebra A T] [IsLocalization U T]
    {ι : Type v} [Fintype ι] {κ : Type w} [Fintype κ]
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (h : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n) (M : ℕ) (hh : ∀ i, (h i).IsHomogeneous M)
    (he : Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh))) :
    ∃ s : U,
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s.val)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.Away s.val)
        (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh)) := by
  let I := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg
  let J := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal h M hh
  let target : ι ⊕ κ → HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n) := Sum.elim (fun _ => J) (fun _ => I)
  let polys : ι ⊕ κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing A n := Sum.elim g h
  let degree : ι ⊕ κ → ℕ := Sum.elim (fun _ => N) (fun _ => M)
  have hdegree : ∀ i, (polys i).IsHomogeneous (degree i) := by
    intro i
    cases i with
    | inl i => exact hg i
    | inr i => exact hh i
  have hmem (i : ι ⊕ κ) : MvPolynomial.map (algebraMap A T) (polys i) ∈
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := T) (target i))).toIdeal := by
    cases i with
    | inl i => exact he ▸ GeneratedSaturationNeighborhood.GradedHilbert.mapped_generator_mem_projectiveSaturation T g N hg i
    | inr i => exact he.symm ▸ GeneratedSaturationNeighborhood.GradedHilbert.mapped_generator_mem_projectiveSaturation T h M hh i
  obtain ⟨s, hsm⟩ := LocalizationSaturationMembership.GradedHilbert.finite_saturation_membership_localization_descent U T target polys degree hdegree hmem
  refine ⟨s, le_antisymm ?_ ?_⟩
  · exact Saturation.PrimeDescent.GradedHilbert.generatedIdeal_le_saturation_of_mapped_generators (Localization.Away s.val) g N hg J
      (fun i => hsm (.inl i))
  · exact Saturation.PrimeDescent.GradedHilbert.generatedIdeal_le_saturation_of_mapped_generators (Localization.Away s.val) h M hh I
      (fun i => hsm (.inr i))

theorem nativeFamily_equality_localization_neighborhood
    {S : Scheme.{u}} (a : Spec (.of A) ⟶ S)
    (F G : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (U : Submonoid A) (T : Type u) [CommRing T] [Algebra A T] [IsLocalization U T]
    (h : Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A T)) F =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A T)) G) :
    ∃ s : U, Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A (Localization.Away s.val))) F =
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
        (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap A (Localization.Away s.val))) G := by
  let E := Intrinsic.AffineEquationModel.GradedHilbert.nativeAffineEquations a F
  let D := Intrinsic.AffineEquationModel.GradedHilbert.nativeAffineEquations a G
  have he := congrArg (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫ a)) h
  rw [Intrinsic.FiniteEquationCoordinates.GradedHilbert.nativeFiniteEquations_baseChange_coordinates E, Intrinsic.FiniteEquationCoordinates.GradedHilbert.nativeFiniteEquations_baseChange_coordinates D] at he
  obtain ⟨s, hsat⟩ := generated_projectiveSaturation_equality_localization_neighborhood U T
    E.generators E.degree E.homogeneous D.generators D.degree D.homogeneous he
  refine ⟨s, ?_⟩
  apply Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s.val))) ≫ a)
  rw [Intrinsic.FiniteEquationCoordinates.GradedHilbert.nativeFiniteEquations_baseChange_coordinates E, Intrinsic.FiniteEquationCoordinates.GradedHilbert.nativeFiniteEquations_baseChange_coordinates D]
  exact hsat

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LocalizationFamilyEqualityNeighborhood.GradedHilbert
