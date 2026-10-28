import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ResiduePolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.NoetherianIdealRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernelRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap

/-! # Noetherian Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.NoetherianInjectivity.GradedHilbert

noncomputable section

/-! Over noetherian affine tests, the actual native family determines its
normalized Hilbert parameter, including all nonreduced directions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {R : Type u} [CommRing R] [IsNoetherianRing R]

theorem normalizedHilbertNativeFamily_noetherian_parameter_injective
    (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of R) ⟶ S)
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (y : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart b S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f)))
    (hy : y ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op (Over.mk f)))
    (hF : IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx = IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily b S q y hy) :
    x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = y ≫ Grassmannian.Gluing.grassmannianChartOverMap b S := by
  let F := IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx
  let G := IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily b S q y hy
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let J := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f G
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f G
  have hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F
  have hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f G
  have hsx : Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (AffineCoordinates.GradedHilbert.affineChartMatrix a f x)) = I :=
    (AffineCoordinates.GradedHilbert.normalizedHilbertNativeFamily_affine_coordinates a f q x hx).symm
  have hsy : Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b (AffineCoordinates.GradedHilbert.affineChartMatrix b f y)) = J :=
    (AffineCoordinates.GradedHilbert.normalizedHilbertNativeFamily_affine_coordinates b f q y hy).symm
  have hex := Normalized.NoetherianIdealRecovery.GradedHilbert.normalizedNoetherianIdeal_eq_degreeGenerated a _ (AffineCoordinates.GradedHilbert.affineChartMatrix_normalized a f x)
    I hI hsx P (ResiduePolynomial.GradedHilbert.normalizedHilbertNativeFamily_residue_polynomial a f q P hP x hx) hN hr
  have hey := Normalized.NoetherianIdealRecovery.GradedHilbert.normalizedNoetherianIdeal_eq_degreeGenerated b _ (AffineCoordinates.GradedHilbert.affineChartMatrix_normalized b f y)
    J hJ hsy P (ResiduePolynomial.GradedHilbert.normalizedHilbertNativeFamily_residue_polynomial b f q P hP y hy) hN hr
  have hIJ : I = J := congrArg (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f) hF
  have he := hex.trans ((congrArg (fun L : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal L N) hIJ).trans hey.symm)
  have hsections := congrArg
    (fun L : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => L.map
      (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) he
  rw [Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map, Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map,
    Affine.ChartMatrixSections.GradedHilbert.affineChartMatrix_map_sections, Affine.ChartMatrixSections.GradedHilbert.affineChartMatrix_map_sections] at hsections
  exact (Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq a b x y).mpr
    ((Normalized.PolynomialKernelRecovery.GradedHilbert.normalizedPolynomialIdeal_eq_iff_kernel_eq a b _ _
      (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S x) (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b S y)).mp hsections)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.NoetherianInjectivity.GradedHilbert
