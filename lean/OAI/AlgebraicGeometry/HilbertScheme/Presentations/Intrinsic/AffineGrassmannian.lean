import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeCoordinateGrassmannian
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicCoefficientBaseChange

/-! # Affine Grassmannian -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert

noncomputable section

/-! Canonical Grassmannian points of native polynomial families over
noetherian affine tests, with the original relative base retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {S : Scheme.{u}} {n : ℕ}
variable (f : Spec (.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
variable (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
variable (N : ℕ) (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)

def nativeAffineCoordinateGrassmannian : Module.Grassmannian R (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N → R) (Fintype.card ι) := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  have hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal N) :=
    Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I hI P hP N ((le_max_left _ _).trans hN)
  exact DegreeCoordinateGrassmannian.GradedHilbert.degreeCoordinateGrassmannian I
    (fun p => (Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I hI P hP N hN p).trans hr.symm)

omit [DecidableEq ι] in
theorem nativeAffineCoordinateGrassmannian_toSubmodule :
    (nativeAffineCoordinateGrassmannian f F P hP N hN ι hr).toSubmodule =
      DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) N := rfl

def nativeAffineHilbertGrassmannianPoint :
    Over.mk f ⟶ Presentations.Grassmannian.Gluing.grassmannianOver (ι := ι) (ν := Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) S :=
  Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (nativeAffineCoordinateGrassmannian f F P hP N hN ι hr)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert
