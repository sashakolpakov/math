import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannian

/-! # Affine Grassmannian Naturality -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannianNaturality.GradedHilbert

noncomputable section

/-! Canonical Grassmannian points of native noetherian families commute
with changes of noetherian affine test ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
variable {S : Scheme.{u}} {n : ℕ}
variable (f : Spec (.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
variable (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
variable (N : ℕ) (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) (φ : R →+* A)

omit [DecidableEq ι] in
theorem nativeAffineCoordinateGrassmannian_baseChange :
    Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ (AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f F P hP N hN ι hr) =
      AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F) P
        (Noetherian.IntrinsicCoefficientBaseChange.GradedHilbert.noetherian_canonical_residue_polynomial_baseChange f F P hP φ) N hN ι hr := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let : Algebra R A := φ.toAlgebra
  apply Module.Grassmannian.ext
  change Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap R A) (DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N) =
    DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F)) N
  rw [DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations_baseChange, Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  apply congrArg (Submodule.map (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis A n N).equivFun.toLinearMap)
  exact (Uniform.SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F)
    P hP A N ((le_max_left _ _).trans hN)).symm

theorem nativeAffineHilbertGrassmannianPoint_natural :
    Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ ≫ AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint f F P hP N hN ι hr =
      AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F) P
        (Noetherian.IntrinsicCoefficientBaseChange.GradedHilbert.noetherian_canonical_residue_polynomial_baseChange f F P hP φ) N hN ι hr := by
  rw [AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint, AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint,
    Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint_natural, nativeAffineCoordinateGrassmannian_baseChange]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannianNaturality.GradedHilbert
