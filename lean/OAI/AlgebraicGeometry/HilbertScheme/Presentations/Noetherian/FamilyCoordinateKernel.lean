import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.OverCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannian

/-! # Family Coordinate Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.FamilyCoordinateKernel.GradedHilbert

noncomputable section

/-! After any coefficient extension, the noetherian family's canonical
Grassmannian quotient has the actual pulled-back family's degree kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.OverCoordinateBaseChange.Grassmannian

universe u
variable {A R : Type u} [CommRing A] [IsNoetherianRing A] [CommRing R]
variable {S : Scheme.{u}} {n N : ℕ} {ι : Type u} [Fintype ι]

theorem noetherian_native_coordinate_baseChange_kernel
    (f : Spec (.of A) ⟶ S) (g : Spec (.of R) ⟶ S)
    (b : Over.mk g ⟶ Over.mk f) (φ : A →+* R)
    (hb : Spec.map (CommRingCat.ofHom φ) = b.left)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum A, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ (Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f F P hP N hN ι hr)).toSubmodule =
      DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n g (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F)) N := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let : Algebra A R := φ.toAlgebra
  change Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (algebraMap A R) (DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I N) =
    DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n g (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F)) N
  rw [DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations_baseChange, Affine.OverCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_over_baseChange f g b φ hb F]
  apply congrArg (Submodule.map (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.toLinearMap)
  exact (Uniform.SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F)
    P hP R N ((le_max_left _ _).trans hN)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.FamilyCoordinateKernel.GradedHilbert
