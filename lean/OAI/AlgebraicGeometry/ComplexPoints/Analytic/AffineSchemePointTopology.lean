import OAI.AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Affine Scheme Point Topology -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology

noncomputable section

/-!
# Ordinary point topology on arbitrary affine complex schemes

The canonical relative spectrum isomorphism identifies every affine scheme
over `Spec ℂ` with the spectrum of its actual global-section algebra. Combining
that isomorphism with the proved affine point topology gives a homeomorphism,
not just a set-theoretic equivalence. Its compatibility with arbitrary affine
scheme morphisms is proved below.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The native points of any affine complex scheme have the ordinary topology
of complex-algebra characters of its actual global sections. -/
def affineNativePointHomeomorph (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] :
    SchemePointHomeomorphs.schemeComplexPoints X ≃ₜ Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) where
  toEquiv := Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X
  continuous_toFun := by
    change Continuous (fun p : SchemePointHomeomorphs.schemeComplexPoints X =>
      (SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤)).symm (p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom))
    exact (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).symm.continuous.comp
      (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom)
  continuous_invFun := by
    change Continuous (fun x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤) =>
      SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) x ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv)
    exact (SchemePointHomeomorphs.schemeComplexPoints.continuous_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv).comp
      (SchemePointHomeomorphs.affineSchemePointHomeomorph Γ(X.left, ⊤)).continuous

@[simp]
theorem affineNativePointHomeomorph_apply (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    affineNativePointHomeomorph X p = Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X p := rfl

@[simp]
theorem affineNativePointHomeomorph_symm_apply (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints Γ(X.left, ⊤)) :
    (affineNativePointHomeomorph X).symm x =
      SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) x ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv := rfl

/-- Applying the affine point correspondence recovers composition with the
canonical spectrum isomorphism. -/
@[simp]
theorem affineSchemePointEquiv_affineNativePointHomeomorph
    (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤) (affineNativePointHomeomorph X p) =
      p ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom :=
  (SchemePointHomeomorphs.affineSchemePointEquiv Γ(X.left, ⊤)).apply_symm_apply _

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsAffine X.left] [IsAffine Y.left]

/-- The algebra homomorphism corresponding to an affine scheme morphism in
the canonical global-section presentations. -/
abbrev affineCoordinateHom (f : X ⟶ Y) : Γ(Y.left, ⊤) →ₐ[ℂ] Γ(X.left, ⊤) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom f

@[simp]
theorem affineAlgHomOverSpecEquiv_affineCoordinateHom (f : X ⟶ Y) :
    Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ Γ(Y.left, ⊤) Γ(X.left, ⊤) (affineCoordinateHom f) =
      (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ≫ f ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_over f

/-- The coordinate homomorphism is the existing pullback on global sections. -/
theorem affineCoordinateHom_toRingHom (f : X ⟶ Y) :
    (affineCoordinateHom f).toRingHom = f.left.appTop.hom :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineAppTopAlgHom_toRingHom f

/-- Under the canonical affine homeomorphisms, every actual affine scheme map
acts by precomposition with its corresponding complex-algebra homomorphism. -/
theorem affineNativePointHomeomorph_map (f : X ⟶ Y) (p : SchemePointHomeomorphs.schemeComplexPoints X) :
    affineNativePointHomeomorph Y (SchemePointHomeomorphs.schemeComplexPoints.map f p) =
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (affineCoordinateHom f) (affineNativePointHomeomorph X p) :=
  Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv_natural f p

/-- The same naturality formula as an equality of point maps. -/
theorem schemePointMap_eq_affineCoordinates (f : X ⟶ Y) :
    SchemePointHomeomorphs.schemeComplexPoints.map f =
      (affineNativePointHomeomorph Y).symm ∘
        Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (affineCoordinateHom f) ∘
          affineNativePointHomeomorph X := by
  funext p
  apply (affineNativePointHomeomorph Y).injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply,
    affineNativePointHomeomorph_map]

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology
