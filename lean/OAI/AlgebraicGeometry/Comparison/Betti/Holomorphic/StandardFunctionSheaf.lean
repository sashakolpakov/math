import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StalkGerms
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold
import Mathlib.Geometry.Manifold.Sheaf.Smooth

/-! # Standard Function Sheaf -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StandardFunctionSheaf.AnalyticLocal

noncomputable section

/-! The actual coefficient-function sheaf agrees with the standard
complex smooth-function sheaf, preserving its stalk germs. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionManifold

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

def holomorphicFunctionContMDiffEquiv (U : Opens E) :
    FunctionPure.holomorphicFunctions U ≃ₐ[ℂ] C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯ where
  toFun f := ⟨f.val, (SectionManifold.holomorphicSection_iff_contMDiff U f.val).mp f.property⟩
  invFun f := ⟨f.val, (SectionManifold.holomorphicSection_iff_contMDiff U f.val).mpr f.property⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply ContMDiffMap.ext; intro x; rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def holomorphicStandardFunctionPresheafIso :
    FunctionSheaf.holomorphicFunctionPresheaf E ≅ smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ :=
  NatIso.ofComponents (fun U => (holomorphicFunctionContMDiffEquiv E U.unop).toRingEquiv.toCommRingCatIso)
    (by
      intro U V f
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      apply ContMDiffMap.ext
      intro x
      rfl)

def standardHolomorphicStalkEquiv [FiniteDimensional ℂ E] (x : E) :
    (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ).stalk x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x :=
  let i : (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ).stalk x ≅
      (FunctionSheaf.holomorphicFunctionPresheaf E).stalk x :=
    ((TopCat.Presheaf.stalkFunctor (X := TopCat.of E) CommRingCat x).mapIso
      (holomorphicStandardFunctionPresheafIso E)).symm
  let j : (smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ).stalk x ≃+*
      (FunctionSheaf.holomorphicFunctionPresheaf E).stalk x :=
    { i.hom.hom, ((forget CommRingCat).mapIso i).toEquiv with }
  j.trans (StalkGerms.AnalyticLocal.holomorphicFunctionStalkEquiv E x)

theorem standardHolomorphicStalkEquiv_germ [FiniteDimensional ℂ E] (x : E) (U : Opens E)
    (hx : x ∈ U) (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ), ℂ⟯) :
    standardHolomorphicStalkEquiv E x ((smoothPresheafCommRing 𝓘(ℂ, E) 𝓘(ℂ) E ℂ).germ U x hx f) =
      SectionGerms.AnalyticLocal.holomorphicSectionGerm U x hx ((holomorphicFunctionContMDiffEquiv E U).symm f) := by
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply (X := TopCat.of E)
    U x hx (holomorphicStandardFunctionPresheafIso E).inv f
  exact (congrArg (StalkMap.AnalyticLocal.holomorphicStalkToGerm E x) h).trans
    (StalkMap.AnalyticLocal.holomorphicStalkToGerm_germ_apply E x U hx ((holomorphicFunctionContMDiffEquiv E U).symm f))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StandardFunctionSheaf.AnalyticLocal
