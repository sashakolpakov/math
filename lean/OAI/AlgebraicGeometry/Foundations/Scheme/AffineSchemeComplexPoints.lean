import OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

/-! # Affine Scheme Complex Points -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints

noncomputable section

/-!
# Complex points of an affine scheme and its global sections

The algebra on global sections and the isomorphism with their spectrum are the
canonical mathlib constructions over the given complex structure morphism.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The global-section algebra induced by the specified complex structure map. -/
instance affineOverGammaAlgebra (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    Algebra ℂ Γ(X.left, ⊤) :=
  (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom.toAlgebra

/-- An affine complex scheme is isomorphic over `Spec ℂ` to the spectrum of its
actual global-section algebra. -/
def affineOverIso (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    X ≅ AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤) :=
  Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤))) = X.hom
    change X.left.isoSpec.hom ≫ Spec.map (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)) = X.hom
    simp)

@[simp]
theorem affineOverIso_hom_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (affineOverIso X).hom.left = X.left.isoSpec.hom := rfl

@[simp]
theorem affineOverIso_inv_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (affineOverIso X).inv.left = X.left.isoSpec.inv := rfl

/-- Native relative complex points of an affine scheme are exactly the
complex-algebra characters of its global sections. -/
def affineNativePointEquiv (X : Over ProjectiveSpace.complexBase) [IsAffine X.left] :
    (Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) ≃ AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) where
  toFun p := (AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤)).symm
    (p ≫ (affineOverIso X).hom)
  invFun x := AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) x ≫ (affineOverIso X).inv
  left_inv p := by simp
  right_inv x := by simp

@[simp]
theorem affineNativePointEquiv_symm_left (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (x : AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤)) :
    ((affineNativePointEquiv X).symm x).left =
      Spec.map (CommRingCat.ofHom x.toRingHom) ≫ X.left.isoSpec.inv := by
  change (AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤) x).left ≫ X.left.isoSpec.inv = _
  rw [AffineComplexPoints.affineComplexPointsOverEquiv_left]

/-- The character corresponding to a native point has the usual spectrum map. -/
theorem affineNativePointEquiv_spec (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    Spec.map (CommRingCat.ofHom (affineNativePointEquiv X p).toRingHom) =
      p.left ≫ X.left.isoSpec.hom := by
  change Spec.map (CommRingCat.ofHom
    ((AffineComplexPoints.affineComplexPointsOverEquiv Γ(X.left, ⊤)).symm
      (p ≫ (affineOverIso X).hom)).toRingHom) = _
  rw [← AffineComplexPoints.affineComplexPointsOverEquiv_left, Equiv.apply_symm_apply]
  rfl

/-- Pullback on global sections, bundled as a complex-algebra homomorphism. -/
def affineAppTopAlgHom {X Y : Over ProjectiveSpace.complexBase} [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) :=
  (AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤)).symm
    ((affineOverIso X).inv ≫ f ≫ (affineOverIso Y).hom)

/-- The coordinate homomorphism gives precisely the conjugated scheme morphism. -/
theorem affineAppTopAlgHom_over {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤) (affineAppTopAlgHom f) =
      (affineOverIso X).inv ≫ f ≫ (affineOverIso Y).hom :=
  (AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤)).apply_symm_apply _

/-- This algebra homomorphism really is the existing pullback on global sections. -/
theorem affineAppTopAlgHom_toRingHom {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    (affineAppTopAlgHom f).toRingHom = f.left.appTop.hom := by
  have h := congrArg Over.Hom.left (affineAppTopAlgHom_over f)
  have hs : Spec.map (CommRingCat.ofHom (affineAppTopAlgHom f).toRingHom) =
      Spec.map f.left.appTop := by
    calc
      _ = X.left.isoSpec.inv ≫ f.left ≫ Y.left.isoSpec.hom := by
        simpa only [AffineComplexPoints.affineAlgHomOverSpecEquiv_left, Over.comp_left,
          affineOverIso_inv_left, affineOverIso_hom_left] using h
      _ = _ := by
        rw [← Scheme.isoSpec_hom_naturality f.left]
        simp
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)

@[simp]
theorem affineAppTopAlgHom_apply {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) (a : Γ(Y.left, ⊤)) :
    affineAppTopAlgHom f a = f.left.appTop a :=
  congrArg (fun h : Γ(Y.left, ⊤) →+* Γ(X.left, ⊤) => h a)
    (affineAppTopAlgHom_toRingHom f)

/-- Evaluating the character of a scheme point is pullback of the section,
followed by the canonical identification of sections of `Spec ℂ` with `ℂ`. -/
theorem affineNativePointEquiv_toRingHom (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    (affineNativePointEquiv X p).toRingHom =
      (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom := by
  have hcat : (CommRingCat.ofHom (affineNativePointEquiv X p).toRingHom :
      Γ(X.left, ⊤) ⟶ CommRingCat.of ℂ) =
      p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    apply (cancel_epi (Scheme.ΓSpecIso Γ(X.left, ⊤)).hom).mp
    rw [← Scheme.ΓSpecIso_naturality, affineNativePointEquiv_spec]
    simp only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop, Category.assoc]
  exact congrArg CommRingCat.Hom.hom hcat

theorem affineNativePointEquiv_eval (X : Over ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) (a : Γ(X.left, ⊤)) :
    affineNativePointEquiv X p a =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appTop a) :=
  congrArg (fun h : Γ(X.left, ⊤) →+* ℂ => h a) (affineNativePointEquiv_toRingHom X p)

/-- The native-point/global-section correspondence is natural in affine
complex schemes. -/
theorem affineNativePointEquiv_natural {X Y : Over ProjectiveSpace.complexBase}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    (p : Over.mk (𝟙 ProjectiveSpace.complexBase) ⟶ X) :
    affineNativePointEquiv Y (p ≫ f) =
      (affineNativePointEquiv X p).comp (affineAppTopAlgHom f) := by
  ext a
  simp only [AlgHom.comp_apply, affineNativePointEquiv_eval,
    affineAppTopAlgHom_apply, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

end

end OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
