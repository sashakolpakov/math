import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorBoundedComplex
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion

/-! # Saturated Tensor -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedTensor.GradedHilbert

noncomputable section

/-! Uniform injectivity of saturated projective coordinates persists under tensoring with every coefficient module. -/

open _root_.MvPolynomial TensorProduct _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorIrrelevantTorsion.ProjectiveCech

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hSat hP in
theorem uniform_saturated_augmentation_lTensor_injective (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d)
    (S : Type v) [AddCommGroup S] [Module R S] :
    Function.Injective ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0).lTensor S) := by
  apply TensorBoundedComplex.lTensor_augmentation_injective_of_bounded_exact R (n + 1)
    (fun q => ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) q)
    (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ))
  · intro q
    exact Cech.FlatAugmentation.ProjectiveCech.moduleCechTermDifferential_exact R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) q
      (ProjectiveAugmentation.GradedHilbert.uniform_projective_cech_exact I P hP (d : ℤ) (by exact_mod_cast hd) q)
  · exact ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (n + 1 + 2) (by simp only [Fintype.card_fin]; omega)
  · exact SaturatedCechAugmentation.GradedHilbert.saturatedCechAugmentation_injective I hSat d
  · intro q hq _
    apply ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) q (by omega)
    intro s hs
    let : Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I s hs
    exact EventualDegreeFlatness.ProjectiveCech.moduleChartDegree_flat_of_zero R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s hs (d : ℤ) (Int.natCast_nonneg d)

include hSat hP in
theorem uniform_saturated_sectionMap_lTensor_injective (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d)
    (S : Type v) [AddCommGroup S] [Module R S] :
    Function.Injective ((Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).lTensor S) := by
  rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  exact (Cech.TermTensorInclusion.ProjectiveCech.moduleCechTermSubtype_lTensor_injective R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
    (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 1 S).comp
    ((uniform_saturated_augmentation_lTensor_injective I hSat P hP d hd S).comp
      (Cech.AugmentationMap.ProjectiveCech.moduleAugmentationToTerm_lTensor_injective R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) S))

include hSat hP in
theorem uniform_saturated_tensor_no_irrelevant_torsion (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d)
    (S : Type v) [AddCommGroup S] [Module R S] (x : S ⊗[R] Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ))
    (hx : ∀ i : Fin (n + 1), ∃ k : ℕ,
      ((TensorFractionTorsion.GradedModules.moduleScalarEnd (R := R) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (X (R := R) i ^ k)).lTensor S)
        (((Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)).subtype.lTensor S) x) = 0) : x = 0 := by
  apply uniform_saturated_sectionMap_lTensor_injective I hSat P hP d hd S
  rw [LinearMap.map_zero]
  apply (TensorProduct.piRight R R S (fun s : Finset (Fin (n + 1)) =>
    Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) s)).injective
  rw [LinearEquiv.map_zero]
  funext s
  rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_tensor_coordinate, Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_proj]
  by_cases hs : s.card = 1
  · rw [ite_eq_left hs, LinearMap.lTensor_comp_apply]
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
    obtain ⟨k, hk⟩ := hx i
    exact TensorFractionTorsion.GradedModules.tensorFraction_zero_of_power_torsion (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)
      (X i) (LaurentMonomials.ProjectiveCech.inversionMonomial R (s.erase i)) (EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi) S _ k hk
  · rw [ite_eq_right hs, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturatedTensor.GradedHilbert
