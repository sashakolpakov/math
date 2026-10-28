import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveIdealCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ContainmentCoefficientIdeal

/-! # Affine Containment Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentIdeal.GradedHilbert

noncomputable section

/-! A native flat projective family over an affine noetherian test
has an actual coefficient ideal for containment in any fixed ambient
ideal sheaf, with the exact criterion on every affine coefficient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (n : ℕ) {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (a : Spec (CommRingCat.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData)

theorem exists_nativeAffineContainmentIdeal :
    ∃ J : Ideal R, ∀ (A : Type u) [CommRing A] (φ : R →+* A),
      J ≤ RingHom.ker φ ↔
        K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ)) ≤
          (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F).val := by
  let I := Affine.ProjectiveIdealCoordinates.GradedHilbert.affineProjectiveIdealCoordinates n a F.val
  let L := Affine.ProjectiveIdealCoordinates.GradedHilbert.affineProjectiveIdealCoordinates n a K
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n a F
  obtain ⟨J, hJ⟩ := Projective.ContainmentCoefficientIdeal.GradedHilbert.exists_projectiveContainmentCoefficientIdeal I L
  refine ⟨J, ?_⟩
  intro A _ φ
  let : Algebra R A := φ.toAlgebra
  have hc : J ≤ RingHom.ker φ ↔
      Projective.Saturation.GradedHilbert.projectiveSaturation (L.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) ≤
        Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := hJ A
  have ho := Affine.ProjectiveIdealCoordinates.GradedHilbert.affineProjectiveIdealCoordinates_le_iff n (Spec.map (CommRingCat.ofHom φ) ≫ a)
    (K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ)))
    (F.val.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ)))
  rw [Affine.ProjectiveIdealCoordinates.GradedHilbert.affineProjectiveIdealCoordinates_baseChange, Affine.ProjectiveIdealCoordinates.GradedHilbert.affineProjectiveIdealCoordinates_baseChange] at ho
  exact hc.trans ho

def nativeAffineContainmentIdeal : Ideal R := (exists_nativeAffineContainmentIdeal n a F K).choose

theorem nativeAffineContainmentIdeal_spec (A : Type u) [CommRing A] (φ : R →+* A) :
    nativeAffineContainmentIdeal n a F K ≤ RingHom.ker φ ↔
      K.comap (Hilbert.Functor.ambientMap (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ)) ≤
        (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F).val :=
  (exists_nativeAffineContainmentIdeal n a F K).choose_spec A φ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.AffineContainmentIdeal.GradedHilbert
