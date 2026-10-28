import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionSheaf
import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-! # Intrinsic Function Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicFunctionSheaf

noncomputable section

/-! The coefficient function sheaf is the standard complex smooth-function sheaf used for analytification. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicFunctionContMDiffEquiv (U : Opens E) :
    FunctionPure.holomorphicFunctions U ≃ₐ[ℂ] C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ where
  toFun := SectionManifold.holomorphicSectionContMDiffEquiv (F := ℂ) U
  invFun := (SectionManifold.holomorphicSectionContMDiffEquiv (F := ℂ) U).symm
  left_inv := (SectionManifold.holomorphicSectionContMDiffEquiv (F := ℂ) U).left_inv
  right_inv := (SectionManifold.holomorphicSectionContMDiffEquiv (F := ℂ) U).right_inv
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def nativeHolomorphicFunctionPresheafIso (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    FunctionSheaf.holomorphicFunctionPresheaf E ≅ smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ :=
  NatIso.ofComponents
    (fun U => (holomorphicFunctionContMDiffEquiv U.unop).toRingEquiv.toCommRingCatIso) (by
      intro U V f
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      apply ContMDiffMap.ext
      intro x
      rfl)

theorem nativeHolomorphicFunctionPresheafIso_apply (U : Opens E)
    (a : FunctionPure.holomorphicFunctions U) (x : U) :
    ((nativeHolomorphicFunctionPresheafIso E).hom.app (op U) a).val x = a.val x := rfl

def nativeHolomorphicFunctionSheafIso (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    FunctionSheaf.holomorphicFunctionSheaf E ≅ smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ :=
  (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology E) CommRingCat).preimageIso
    (nativeHolomorphicFunctionPresheafIso E)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntrinsicFunctionSheaf
