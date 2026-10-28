import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
import OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Intrinsic Scheme Diffeomorph -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSchemeDiffeomorph

noncomputable section

/-!
# Diffeomorphisms induced by actual complex scheme isomorphisms

The manifold structures are the derived native smooth scheme structures.
Source and target retain their own function-field dimensions. Smoothness of
both directions comes from the proved smoothness of actual scheme morphisms.
-/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
variable [IsIntegral Z.left] [Smooth Z.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- An actual isomorphism of smooth integral complex schemes induces an
analytic diffeomorphism of their constructed native point manifolds. -/
def nativeSchemeDiffeomorph (e : X ≅ Y) (r : ℕ∞ω) :
    Diffeomorph (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY))
      (SchemePointHomeomorphs.schemeComplexPoints X) (SchemePointHomeomorphs.schemeComplexPoints Y) r where
  toEquiv := (SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph e).toEquiv
  contMDiff_toFun := IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map e.hom r
  contMDiff_invFun := IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map e.inv r

/-- The underlying real smooth manifolds are diffeomorphic by the same
actual scheme-point maps. -/
def nativeSchemeRealDiffeomorph (e : X ≅ Y) (r : ℕ∞ω) :
    Diffeomorph (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY))
      (SchemePointHomeomorphs.schemeComplexPoints X) (SchemePointHomeomorphs.schemeComplexPoints Y) r where
  toEquiv := (SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph e).toEquiv
  contMDiff_toFun := IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map e.hom r
  contMDiff_invFun := IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map e.inv r

@[simp]
theorem nativeSchemeDiffeomorph_apply (e : X ≅ Y) (r : ℕ∞ω)
    (p : SchemePointHomeomorphs.schemeComplexPoints X) : nativeSchemeDiffeomorph e r p = p ≫ e.hom := rfl

@[simp]
theorem nativeSchemeRealDiffeomorph_apply (e : X ≅ Y) (r : ℕ∞ω)
    (p : SchemePointHomeomorphs.schemeComplexPoints X) : nativeSchemeRealDiffeomorph e r p = p ≫ e.hom := rfl

@[simp]
theorem nativeSchemeDiffeomorph_symm_apply (e : X ≅ Y) (r : ℕ∞ω)
    (p : SchemePointHomeomorphs.schemeComplexPoints Y) : (nativeSchemeDiffeomorph e r).symm p = p ≫ e.inv := rfl

@[simp]
theorem nativeSchemeRealDiffeomorph_symm_apply (e : X ≅ Y) (r : ℕ∞ω)
    (p : SchemePointHomeomorphs.schemeComplexPoints Y) : (nativeSchemeRealDiffeomorph e r).symm p = p ≫ e.inv := rfl

/-- Forgetting smoothness recovers the already established native point
homeomorphism induced by the scheme isomorphism. -/
@[simp]
theorem nativeSchemeDiffeomorph_toHomeomorph (e : X ≅ Y) (r : ℕ∞ω) :
    (nativeSchemeDiffeomorph e r).toHomeomorph = SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph e := by
  ext p
  rfl

@[simp]
theorem nativeSchemeRealDiffeomorph_toHomeomorph (e : X ≅ Y) (r : ℕ∞ω) :
    (nativeSchemeRealDiffeomorph e r).toHomeomorph = SchemePointHomeomorphs.schemeComplexPoints.isoHomeomorph e := by
  ext p
  rfl

@[simp]
theorem nativeSchemeDiffeomorph_symm (e : X ≅ Y) (r : ℕ∞ω) :
    (nativeSchemeDiffeomorph e r).symm = nativeSchemeDiffeomorph e.symm r := by
  ext p
  rfl

@[simp]
theorem nativeSchemeRealDiffeomorph_symm (e : X ≅ Y) (r : ℕ∞ω) :
    (nativeSchemeRealDiffeomorph e r).symm = nativeSchemeRealDiffeomorph e.symm r := by
  ext p
  rfl

/-- The construction respects composition of actual scheme isomorphisms. -/
@[simp]
theorem nativeSchemeDiffeomorph_trans (e : X ≅ Y) (f : Y ≅ Z) (r : ℕ∞ω) :
    nativeSchemeDiffeomorph (e.trans f) r =
      (nativeSchemeDiffeomorph e r).trans (nativeSchemeDiffeomorph f r) := by
  apply Diffeomorph.ext
  intro p
  exact (Category.assoc p e.hom f.hom).symm

@[simp]
theorem nativeSchemeRealDiffeomorph_trans (e : X ≅ Y) (f : Y ≅ Z) (r : ℕ∞ω) :
    nativeSchemeRealDiffeomorph (e.trans f) r =
      (nativeSchemeRealDiffeomorph e r).trans (nativeSchemeRealDiffeomorph f r) := by
  apply Diffeomorph.ext
  intro p
  exact (Category.assoc p e.hom f.hom).symm

end

namespace IntegralProjectiveVariety

local instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.nativeIntegral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    IsIntegral V.toOver.left := V.property

local instance _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.nativeSmooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Smooth V.toOver.hom := V.presentation.smooth

/-- Transporting a smooth integral projective presentation along a genuine
scheme isomorphism preserves its native complex manifold up to analytic
diffeomorphism. Each side uses its own proved function-field dimension. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.transportIso_diffeomorph (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) (r : ℕ∞ω) :
    Diffeomorph
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
        (V.transportIso e).toOver.hom) → ℂ))
      (𝓘(ℂ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ))
      (SchemePointHomeomorphs.schemeComplexPoints (V.transportIso e).toOver) (SchemePointHomeomorphs.schemeComplexPoints V.toOver) r :=
  nativeSchemeDiffeomorph (V.transportIso_overIso e) r

/-- The same presentation transport is a diffeomorphism of the underlying
real smooth manifolds. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.transportIso_realDiffeomorph (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) (r : ℕ∞ω) :
    Diffeomorph
      (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension
        (V.transportIso e).toOver.hom) → ℂ))
      (𝓘(ℝ, Fin (Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.toOver.hom) → ℂ))
      (SchemePointHomeomorphs.schemeComplexPoints (V.transportIso e).toOver) (SchemePointHomeomorphs.schemeComplexPoints V.toOver) r :=
  nativeSchemeRealDiffeomorph (V.transportIso_overIso e) r

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.transportIso_diffeomorph_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) (r : ℕ∞ω) (p : SchemePointHomeomorphs.schemeComplexPoints (V.transportIso e).toOver) :
    V.transportIso_diffeomorph e r p = p ≫ (V.transportIso_overIso e).hom := rfl

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.transportIso_realDiffeomorph_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) (r : ℕ∞ω) (p : SchemePointHomeomorphs.schemeComplexPoints (V.transportIso e).toOver) :
    V.transportIso_realDiffeomorph e r p = p ≫ (V.transportIso_overIso e).hom := rfl

end IntegralProjectiveVariety

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSchemeDiffeomorph
