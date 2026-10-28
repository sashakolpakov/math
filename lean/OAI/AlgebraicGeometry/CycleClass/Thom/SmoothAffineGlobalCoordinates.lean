import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineSchemePointTopology

/-! # Smooth Affine Global Coordinates -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions.Spec

/-! The canonical correspondence between affine characters and actual scheme points is a holomorphic homeomorphism in the established smooth manifolds. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.Smooth ℂ A]

instance instSmoothAffineSpec_proofs : Smooth (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

variable [IsDomain A]

instance instIsIntegralAffineSpec_proofs : IsIntegral (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of A)))

local notation "ModelA" => Fin (OAI.AlgebraicGeometry.Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ
local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Over.hom (OAI.AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))) → ℂ

omit [Algebra.Smooth ℂ A] [IsDomain A] in
theorem affineIdentityPointMap :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) =
      (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A → _) := by
  funext x
  exact Category.comp_id _

theorem affineSchemePointHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A) := by
  rw [← affineIdentityPointMap]
  exact ComplexPoints.Analytic.AffineOpenDifferential.contMDiff_affinePointMap (CommAlgCat.of ℂ A) (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) ω

theorem affineSchemePointHomeomorph_mfderiv_bijective (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Function.Bijective (mfderiv 𝓘(ℂ, ModelA) 𝓘(ℂ, ModelX) (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A) x) := by
  let : IsOpenImmersion (Over.Hom.left (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A))) := by
    change IsOpenImmersion (𝟙 (Spec (CommRingCat.of A)))
    infer_instance
  rw [← affineIdentityPointMap]
  exact ComplexPoints.Analytic.AffineOpenDifferential.mfderiv_affinePointMap_bijective (CommAlgCat.of ℂ A) (𝟙 (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A)) x

theorem affineSchemePointHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelA) ω (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A).symm :=
  HolomorphicHomeomorph.Constructions.homeomorph_symm_analytic (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A)
    (affineSchemePointHomeomorph_analytic A) (affineSchemePointHomeomorph_mfderiv_bijective A)

theorem affineScheme_modelDimension (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A =
      Betti.AffineDimension.Realization.functionFieldDifferentialDimension (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A).hom := by
  simpa only [Module.finrank_fin_fun] using HolomorphicHomeomorph.Constructions.homeomorph_model_finrank (ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointHomeomorph A)
    ((affineSchemePointHomeomorph_analytic A).mdifferentiable (by simp))
    ((affineSchemePointHomeomorph_symm_analytic A).mdifferentiable (by simp)) x

end AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions.Spec

namespace AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions

/-! Canonical global sections give holomorphic affine coordinates on an arbitrary smooth integral affine complex scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions.Spec OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [Smooth X.hom]

instance instSmoothAffineGamma_proofs : Algebra.Smooth ℂ Γ(X.left, ⊤) := by
  rw [← RingHom.smooth_algebraMap]
  change (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom.Smooth
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mp
  simpa only [Spec.map_preimage] using
    (inferInstance : Smooth (X.left.isoSpec.inv ≫ X.hom))

variable [IsIntegral X.left]

local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ

theorem affineNativePointHomeomorph_analytic :
    ContMDiff 𝓘(ℂ, ModelX) 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ Γ(X.left, ⊤)) → ℂ)
      ω (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X) :=
  (Constructions.Spec.affineSchemePointHomeomorph_symm_analytic Γ(X.left, ⊤)).comp
    (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom ω)

theorem affineNativePointHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ Γ(X.left, ⊤)) → ℂ) 𝓘(ℂ, ModelX)
      ω (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).symm :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv ω).comp
    (Constructions.Spec.affineSchemePointHomeomorph_analytic Γ(X.left, ⊤))

theorem affineNative_modelDimension (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom =
      Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ Γ(X.left, ⊤) := by
  simpa only [Module.finrank_fin_fun] using HolomorphicHomeomorph.Constructions.homeomorph_model_finrank (ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X)
    ((affineNativePointHomeomorph_analytic X).mdifferentiable (by simp))
    ((affineNativePointHomeomorph_symm_analytic X).mdifferentiable (by simp)) x

end AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions

end

end OAI
