import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SinglePolynomialChart
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HilbertCoefficientTransport

/-! # Intrinsic Coordinate Ideal -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal

noncomputable section

/-! The native chart ideal is exactly Presentations's homogeneous ideal after the
canonical coefficient isomorphism R ≃ Γ(Spec R). Thus the native graph
Hilbert polynomial is the actual polynomial in the corrected Presentations predicate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

theorem nativeProjectiveDehomogenize_coefficient_map (i : Fin (n + 1))
    (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveDehomogenize i
      (MvPolynomial.map (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom p) =
        Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p) := by
  apply (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).injective
  change (SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i)
    ((SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv (R := R) i).symm
      (SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤) (fun _ : Fin 1 => i)
        (MvPolynomial.map (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom p))) = _
  rw [RingEquiv.apply_symm_apply, ChartCoordinates.PolarizationEmbedding.singleProjectiveChartRingEquiv_awayToSection,
    ChartCoordinates.PolarizationEmbedding.e34_dehomogenize_chart_coordinates, SinglePolynomialChart.PolarizationEmbedding.singlePolynomialChart_dehomogenize,
    SinglePolynomialChart.PolarizationEmbedding.polynomialChartRingHom_mapRingEquiv]

variable {X : Scheme.{u}} (f : X ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem nativeProjectiveCoordinateIdeal_comap :
    (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).comap
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom) =
        HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker := by
  apply HomogeneousIdeal.ext'
  intro d p hp
  change MvPolynomial.map (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom p ∈
    (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal ↔ p ∈ (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker).toIdeal
  rw [IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal, ChartKernelIdeal.PolarizationEmbedding.mem_chartKernelIdeal _ _ (hp.map _),
    HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf, HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.mem_chartHomogeneousIdeal _ hp]
  apply forall_congr'
  intro i
  rw [nativeProjectiveDehomogenize_coefficient_map]
  rfl

theorem nativeProjectiveCoordinateIdeal_eq_e34_map :
    IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f =
      (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf f.ker).map
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom) := by
  rw [← nativeProjectiveCoordinateIdeal_comap f]
  apply HomogeneousIdeal.ext
  exact (Ideal.map_comap_of_surjective _
    (MvPolynomial.map_surjective
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
    (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal f).toIdeal).symm

theorem native_hasHilbertPolynomial_iff_e34 {k : Type u} [Field k]
    {Y : Scheme.{u}} (j : Y ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading k n)) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (IntrinsicCoordinateIdeal.PolarizationEmbedding.nativeProjectiveCoordinateIdeal j).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf j.ker).toIdeal P := by
  have hfield : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let := hfield.toField
  rw [nativeProjectiveCoordinateIdeal_eq_e34_map]
  exact HilbertCoefficientTransport.PolarizationEmbedding.hasHilbertPolynomial_coefficient_map_iff
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.toRingHom
    (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf j.ker) P

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.IntrinsicCoordinateIdeal
