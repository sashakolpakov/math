import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.LocalGlobalFunctions
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MapStalkDetection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity

/-! # Global Functions -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GlobalFunctions.Construction

noncomputable section

/-! Noetherian local constancy extends to a locally Noetherian base
by detection on actual local spectra, retaining all nilpotents. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_affineMap_eq_of_section
    {S X Z : Scheme.{0}} [IsLocallyNoetherian S] [IsAffine Z]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) (g : X ⟶ Z) : g = f ≫ σ ≫ g := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  apply HilbertScheme.Presentations.MapStalkDetection.schemeHom_eq_of_fromSpecStalk
  intro x
  have : IsNoetherianRing (S.presheaf.stalk (f x)) := inferInstance
  let s := S.fromSpecStalk (f x)
  let b := pullback.snd f s
  let σ' : Spec (S.presheaf.stalk (f x)) ⟶ pullback f s :=
    pullback.lift (s ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  have : IsIso b.appTop := LocalGlobalFunctions.Construction.noetherianLocal_globalFunctions_isIso
    (R := S.presheaf.stalk (f x)) b σ' (pullback.lift_snd _ _ _)
  let τ : Spec (X.presheaf.stalk x) ⟶ pullback f s :=
    pullback.lift (X.fromSpecStalk x) (Spec.map (f.stalkMap x))
      (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
  have h := congrArg (fun k => τ ≫ k)
    (AbelianModuli.HilbertConstruction.Global.FunctionsMapRigidity.affineMap_eq_of_globalFunctions_iso b σ' (pullback.lift_snd _ _ _) (pullback.fst f s ≫ g))
  simpa only [τ, b, σ', s, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk_assoc] using h

set_option backward.isDefEq.respectTransparency false in
theorem noetherian_globalFunctions_isIso
    {S X : Scheme.{0}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 _) : IsIso f.appTop := by
  have h := congrArg Scheme.Hom.appTop (noetherian_affineMap_eq_of_section f σ hσ X.toSpecΓ)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h
  have he : σ.appTop ≫ f.appTop = 𝟙 Γ(X, ⊤) := by
    apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
    simpa only [Category.comp_id, Category.assoc] using h.symm
  exact (show Γ(S, ⊤) ≅ Γ(X, ⊤) from {
    hom := f.appTop
    inv := σ.appTop
    hom_inv_id := by rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
    inv_hom_id := he }).isIso_hom

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Noetherian.GlobalFunctions.Construction
