import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MatchingRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValueFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.IsoSlicePullback

/-! # Cech Object Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent

noncomputable section

/-! Native pullback isomorphisms on open intersections give the actual
matching-section line object. Compatibility is measured by the existing
canonical module pullback, so this adapter retains all pullback paths. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {X Y : Scheme.{u}}

def openPullbackIsoValue (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (U : X.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) :=
  OpenModule.IsoValues.openModuleIsoValue f
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M ≪≫ e ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback f).symm.app N) U hU

theorem openPullbackIsoValue_apply (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    openPullbackIsoValue f e U hU s = ModuleValues.openPullbackModuleValue f e.hom U hU s :=
  LinearMap.congr_fun (ModuleValues.openPullbackModuleValue_restriction f e.hom U hU) s

theorem openPullbackModuleValue_natural (f : Y ⟶ X) [IsOpenImmersion f] {M N : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    {U V : X.Opens} (h : V ≤ U) (hU : U ≤ f.opensRange) (hV : V ≤ f.opensRange)
    (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f a V hV (M.presheaf.map (homOfLE h).op s) =
      N.presheaf.map (homOfLE h).op (ModuleValues.openPullbackModuleValue f a U hU s) := by
  rw [← ModuleValues.openPullbackModuleValue_restriction, ← ModuleValues.openPullbackModuleValue_restriction]
  exact OpenModule.MapValues.openModuleMapValue_natural f (ModuleValues.pullbackModuleRestrictionMap f a) h hU hV s

theorem openPullbackModuleValue_identity (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f (𝟙 ((Scheme.Modules.pullback f).obj M)) U hU s = s := by
  rw [← ModuleValues.openPullbackModuleValue_restriction]
  have he : ModuleValues.pullbackModuleRestrictionMap f (𝟙 ((Scheme.Modules.pullback f).obj M)) =
      𝟙 (M.restrict f) := by
    simp only [ModuleValues.pullbackModuleRestrictionMap, Category.id_comp, Iso.hom_inv_id_app]
  rw [he]
  exact OpenModule.MapValueFunctoriality.openModuleMapValue_identity f M U hU s

theorem openPullbackModuleValue_hom_comp (f : Y ⟶ X) [IsOpenImmersion f] {M N P : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (b : (Scheme.Modules.pullback f).obj N ⟶ (Scheme.Modules.pullback f).obj P)
    (U : X.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ModuleValues.openPullbackModuleValue f (a ≫ b) U hU s =
      ModuleValues.openPullbackModuleValue f b U hU (ModuleValues.openPullbackModuleValue f a U hU s) := by
  have hc : ModuleValues.pullbackModuleRestrictionMap f (a ≫ b) =
      ModuleValues.pullbackModuleRestrictionMap f a ≫ ModuleValues.pullbackModuleRestrictionMap f b := by
    simp only [ModuleValues.pullbackModuleRestrictionMap, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← ModuleValues.openPullbackModuleValue_restriction, hc, OpenModule.MapValueFunctoriality.openModuleMapValue_hom_comp,
    ModuleValues.openPullbackModuleValue_restriction, ModuleValues.openPullbackModuleValue_restriction]

theorem openPullbackModuleValue_refine_on {U V : X.Opens} (h : U ≤ V)
    {M N : X.Modules}
    (a : (Scheme.Modules.pullback V.ι).obj M ⟶ (Scheme.Modules.pullback V.ι).obj N)
    (W : X.Opens) (hW : W ≤ U) :
    ModuleValues.openPullbackModuleValue U.ι (Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) a) W
        (by simpa only [Scheme.Opens.opensRange_ι] using hW) =
      ModuleValues.openPullbackModuleValue V.ι a W
        (by simpa only [Scheme.Opens.opensRange_ι] using hW.trans h) := by
  have hUV : W ≤ (X.homOfLE h ≫ V.ι).opensRange := by
    simpa only [X.homOfLE_ι h, Scheme.Opens.opensRange_ι] using hW
  exact (OpenModule.MapRefinement.openPullbackModuleValue_congr (X.homOfLE_ι h)
    (Module.MapPullbackComposition.moduleMapPullbackComp (X.homOfLE h) V.ι a) W hUV _).trans
      (RefinementNaturality.openPullbackModuleValue_comp (X.homOfLE h) V.ι a W hUV)

structure OpenPullbackCechIsos {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (M : ι → X.Modules) where
  iso : ∀ i j, (Scheme.Modules.pullback (U i ⊓ U j).ι).obj (M i) ≅
    (Scheme.Modules.pullback (U i ⊓ U j).ι).obj (M j)
  identity : ∀ i, iso i i = Iso.refl _
  cocycle : ∀ i j k,
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left)) (iso i j).hom ≫
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (iso j k).hom =
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap
      (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (iso i k).hom

namespace OpenPullbackCechIsos
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : OpenPullbackCechIsos U M)

def transitions : OpenModule.MatchingSheaf.OpenModuleTransitions U M where
  compare V i j hi hj := openPullbackIsoValue (U i ⊓ U j).ι (D.iso i j) V
    (by simpa only [Scheme.Opens.opensRange_ι] using le_inf hi hj)
  natural V W h i j hi hj s := by
    rw [openPullbackIsoValue_apply, openPullbackIsoValue_apply]
    exact openPullbackModuleValue_natural _ _ h _ _ s
  identity V i hi s := by
    rw [openPullbackIsoValue_apply, D.identity]
    exact openPullbackModuleValue_identity _ _ _ _ s
  composition V i j k hi hj hk s := by
    let W := (U i ⊓ U j) ⊓ U k
    have hV : V ≤ W := le_inf (le_inf hi hj) hk
    have hW : V ≤ W.ι.opensRange := by simpa only [Scheme.Opens.opensRange_ι] using hV
    let a := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U i ⊓ U j from inf_le_left))
      (D.iso i j).hom
    let b := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U j ⊓ U k from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (D.iso j k).hom
    let c := Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap (show W ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (D.iso i k).hom
    have ha := openPullbackModuleValue_refine_on
      (show W ≤ U i ⊓ U j from inf_le_left) (D.iso i j).hom V hV
    have hb := openPullbackModuleValue_refine_on
      (show W ≤ U j ⊓ U k from le_inf (inf_le_left.trans inf_le_right) inf_le_right)
      (D.iso j k).hom V hV
    have hc := openPullbackModuleValue_refine_on
      (show W ≤ U i ⊓ U k from le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (D.iso i k).hom V hV
    rw [openPullbackIsoValue_apply, openPullbackIsoValue_apply, openPullbackIsoValue_apply,
      ← ha, ← hb, ← hc]
    exact (openPullbackModuleValue_hom_comp W.ι a b V hW s).symm.trans
      (congrArg (fun t => ModuleValues.openPullbackModuleValue W.ι t V hW s) (D.cocycle i j k))

variable (hU : ∀ x : X, ∃ i, x ∈ U i) (L : ∀ i, Line.Bundles.LineBundle (U i).toScheme)
  (r : ∀ i, (M i).restrict (U i).ι ≅ (L i).sheaf)

def lineBundle : Line.Bundles.LineBundle X := D.transitions.lineBundle hU L r

def lineBundle_recovery (i : ι) :
    ((D.lineBundle hU L r).pullback (U i).ι).sheaf ≅ (L i).sheaf :=
  D.transitions.lineBundle_recovery hU L r i

end OpenPullbackCechIsos

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.CechObjectDescent
