import OAI.Geometry.ComplexTorus.RiemannProjectivity.ChartPeriodSmoothness
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion

/-! # Affine Image Algebra Eq -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq.Constructions.AffineImageAlgebra

/-! # RiemannProjectivity: identify a reduced affine algebra from its actual complex-point image -/

open Set

variable {ι : Type*} {A : Type*} [CommRing A] [Algebra ℂ A]

def coordinates (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (q : A →ₐ[ℂ] ℂ) : ι → ℂ :=
  fun i => q (f (MvPolynomial.X i))

theorem eval_coordinates (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (q : A →ₐ[ℂ] ℂ)
    (p : MvPolynomial ι ℂ) : MvPolynomial.eval (coordinates f q) p = q (f p) := by
  have h : MvPolynomial.aeval (coordinates f q) = q.comp f := by
    ext i
    simp [coordinates]
  exact congrArg (fun f : MvPolynomial ι ℂ →ₐ[ℂ] ℂ => f p) h

theorem kernel_eq_vanishingIdeal [Algebra.FiniteType ℂ A] [IsReduced A]
    (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (S : Set (ι → ℂ))
    (hS : range (coordinates f) = S) : RingHom.ker f.toRingHom = MvPolynomial.vanishingIdeal ℂ S := by
  ext p
  constructor
  · intro hp x hx
    rw [← hS] at hx
    obtain ⟨q, rfl⟩ := hx
    change MvPolynomial.eval (coordinates f q) p = 0
    rw [eval_coordinates, show f p = 0 from hp, map_zero]
  · intro hp
    change f p = 0
    apply CharacterSeparationEq.Constructions.CharacterSeparation.eq_zero_of_all_points_zero
    intro q
    rw [← eval_coordinates]
    apply hp
    rw [← hS]
    exact ⟨q, rfl⟩

theorem smooth [Algebra.FiniteType ℂ A] [IsReduced A]
    (f : MvPolynomial ι ℂ →ₐ[ℂ] A) (hf : Function.Surjective f) (S : Set (ι → ℂ))
    (hS : range (coordinates f) = S)
    (hsm : Algebra.Smooth ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S)) : Algebra.Smooth ℂ A := by
  have hker := kernel_eq_vanishingIdeal f S hS
  let : Algebra.Smooth ℂ (MvPolynomial ι ℂ ⧸ RingHom.ker f.toRingHom) := by
    rwa [hker]
  let e : (MvPolynomial ι ℂ ⧸ RingHom.ker f.toRingHom) ≃ₐ[ℂ] A :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  exact Algebra.Smooth.of_equiv e

end Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq.Constructions.AffineImageAlgebra

namespace Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra

/-! # RiemannProjectivity: smooth polynomial coordinate algebras yield smooth native affine schemes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A : Type} [CommRing A] [Algebra ℂ A]
  (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]

def coordinateHom (j : X ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) : A →ₐ[ℂ] Γ(X.left, ⊤) :=
  (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A Γ(X.left, ⊤)).symm ((AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ j)

set_option backward.isDefEq.respectTransparency false in
theorem coordinateHom_spec (j : X ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) :
    Spec.map (CommRingCat.ofHom (coordinateHom X j).toRingHom) = X.left.isoSpec.inv ≫ j.left := by
  have h := congrArg Over.Hom.left
    ((AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A Γ(X.left, ⊤)).apply_symm_apply ((AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ j))
  simpa only [coordinateHom, AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv_left, Over.comp_left,
    AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso_inv_left] using h

set_option backward.isDefEq.respectTransparency false in
theorem coordinateHom_surjective (j : X ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) [IsClosedImmersion j.left] :
    Function.Surjective (coordinateHom X j) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (coordinateHom X j).toRingHom)) := by
    rw [coordinateHom_spec]
    infer_instance
  exact AlgebraicGeometry.Foundations.Scheme.AffineClosedImmersion.ringMap_surjective_of_spec_closedImmersion (CommRingCat.ofHom (coordinateHom X j).toRingHom)

set_option backward.isDefEq.respectTransparency false in
theorem coordinateHom_point (j : X ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A) (q : Γ(X.left, ⊤) →ₐ[ℂ] ℂ) :
    AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv A (q.comp (coordinateHom X j)) =
      (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X).symm q ≫ j := by
  apply Over.OverMorphism.ext
  simp only [AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPointsOverEquiv_left, Over.comp_left, AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_symm_left]
  calc
    Spec.map (CommRingCat.ofHom (q.comp (coordinateHom X j)).toRingHom) =
        Spec.map (CommRingCat.ofHom q.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (coordinateHom X j).toRingHom) := by
      rw [← Spec.map_comp]
      rfl
    _ = (Spec.map (CommRingCat.ofHom q.toRingHom) ≫ X.left.isoSpec.inv) ≫ j.left := by
      rw [coordinateHom_spec, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem smooth_of_algebra [Algebra.Smooth ℂ Γ(X.left, ⊤)] : Smooth X.hom := by
  have : Smooth (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤)).hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact (inferInstance : Algebra.Smooth ℂ Γ(X.left, ⊤))
  rw [← (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.w]
  infer_instance

theorem smooth_of_polynomial_point_image {ι : Type} [Finite ι] [IsReduced X.left]
    (j : X ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ (MvPolynomial ι ℂ)) [IsClosedImmersion j.left]
    (S : Set (ι → ℂ)) (hS : Set.range (AffineImageAlgebra.coordinates (coordinateHom X j)) = S)
    (hsm : Algebra.Smooth ℂ (AffineVanishing.Constructions.AffineVanishingPoints.coordinateRing S)) : Smooth X.hom := by
  have hf := coordinateHom_surjective X j
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := Algebra.FiniteType.of_surjective (coordinateHom X j) hf
  let : Algebra.Smooth ℂ Γ(X.left, ⊤) := AffineImageAlgebra.smooth (coordinateHom X j) hf S hS hsm
  exact smooth_of_algebra X

end Geometry.ComplexTorus.RiemannProjectivity.AffineImageAlgebraEq.Constructions.AffineSchemeAlgebra

end

end OAI
