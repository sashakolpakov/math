/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeneratingSectionFiniteness

/-! # Over Generator Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverGeneratorFiniteness

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {X : Scheme.{u}}

theorem module_finite_restrict_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) := by
  let : IsAffine U.toScheme := hU
  let F := (Scheme.Modules.overEquiv U).functor
  let : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (Scheme.Modules.overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF (Iso.refl _)
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((Scheme.Modules.overFunctorEquiv U).app M) G'
  have : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact GeneratingSectionFiniteness.affine_globalSections_finite_of_generatingSections
    (M.restrict U.ι) G''

theorem module_finite_app_of_over_generators
    (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hfinite : Module.Finite Γ(U.toScheme, ⊤) Γ(M.restrict U.ι, ⊤) :=
    module_finite_restrict_of_over_generators M U hU G
  let eR' := U.ι.appIso (⊤ : U.toScheme.Opens)
  let eR : Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) ≃+* Γ(U.toScheme, ⊤) :=
    eR'.commRingCatIsoToRingEquiv
  let eM' := M.restrictAppIso U.ι ⊤
  let σ : Γ(U.toScheme, ⊤) →+*
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := eR'.inv.hom
  let eM : Γ(M.restrict U.ι, ⊤) →ₛₗ[σ]
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := eM'.hom
      map_add' := eM'.hom.hom.map_add
      map_smul' := by
        intro r x
        change eM'.hom (r • x) = eR'.inv.hom r • eM'.hom x
        exact Scheme.Modules.smul_restrictAppIso_hom_apply U.ι M ⊤ r x }
  have hσ : Function.Surjective σ := by
    change Function.Surjective
      (eR.symm : Γ(U.toScheme, ⊤) →+*
        Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens)))
    exact eR.symm.surjective
  let : RingHomSurjective σ := ⟨hσ⟩
  have heM : Function.Bijective eM := by
    change Function.Bijective eM'.hom
    exact ConcreteCategory.bijective_of_isIso eM'.hom
  have htarget : Module.Finite
      Γ(X, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      Γ(M, U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    (eM.finite_iff_of_bijective heM).mp hfinite
  rw [U.ι_image_top] at htarget
  exact htarget

theorem module_finite_app_of_over_generators_of_le
    (M : X.Modules) [M.IsQuasicoherent]
    {U V : X.Opens} (hVU : V ≤ U) (hV : IsAffineOpen V)
    (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, V) Γ(M, V) := by
  let i : V ⟶ U := homOfLE hVU
  let F := SheafOfModules.overMap X.ringCatSheaf i
  let : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    (SheafOfModules.overMapPushforwardAdj X.ringCatSheaf i).leftAdjoint_preservesColimits
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF
      (SheafOfModules.overMapUnitIso i).symm
  let G'' := SheafOfModules.GeneratingSections.equivOfIso
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app M) G'
  have : G''.IsFiniteType := ⟨by
    change Finite G.I
    infer_instance⟩
  exact module_finite_app_of_over_generators M V hV G''

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverGeneratorFiniteness
