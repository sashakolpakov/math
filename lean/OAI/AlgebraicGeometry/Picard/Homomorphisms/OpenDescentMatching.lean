import OAI.AlgebraicGeometry.Picard.Homomorphisms.DescentMatching
import OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenFrameDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FaithfulLineMorphisms

/-! # Open Descent Matching -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenDescentMatching

noncomputable section

/-! Local descended maps match the original cover on all smaller opens;
faithful pullback then proves their agreement on overlaps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

theorem baseChangedDescentHom_matches
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (s : Y' ⟶ Y) (t : X' ⟶ X)
    (w : t ≫ f = f' ≫ s)
    (bD : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M)
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (hb : ModuleHomBaseChange.Construction.canonicalDescentModuleHom f bD = b)
    (a : (Scheme.Modules.pullback s).obj L ⟶ (Scheme.Modules.pullback s).obj M)
    (ha : (Scheme.Modules.pullback f').map a =
      ModuleHomBaseChange.Construction.canonicalDescentModuleHom f' (ModuleHomBaseChange.Construction.baseChangedDescentHom f f' s t w bD)) :
    ModuleHomTransport.Construction.moduleHomTransport s a f' (t ≫ f) w.symm = ModuleHomTransport.Construction.moduleHomTransport f b t (t ≫ f) rfl := by
  apply DescentMatching.Construction.moduleHom_matching_of_square f f' s t w b a
  change bD.hom PUnit.unit = b at hb
  change (Scheme.Modules.pullback f').map a =
    (ModuleHomBaseChange.Construction.baseChangedDescentHom f f' s t w bD).hom PUnit.unit at ha
  rw [ha, ModuleHomBaseChange.Construction.baseChangedDescentHom_native, hb]
  rfl

theorem openDescentModuleHom_matches (U : Y.Opens)
    (bD : (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M)
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (hb : ModuleHomBaseChange.Construction.canonicalDescentModuleHom f bD = b)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (ha : (Scheme.Modules.pullback (f ∣_ U)).map a = OpenFrameDescent.Construction.openDescentModuleHom f U bD) :
    ModuleHomTransport.Construction.moduleHomTransport U.ι a (f ∣_ U) ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) =
      ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ U).ι ((f ⁻¹ᵁ U).ι ≫ f) rfl :=
  baseChangedDescentHom_matches f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι
    (morphismRestrict_ι f U).symm bD b hb a ha

theorem morphismRestrict_inclusion {U V : Y.Opens} (h : V ≤ U) :
    X.homOfLE (f.preimage_mono h) ≫ (f ∣_ U) = (f ∣_ V) ≫ Y.homOfLE h := by
  apply (cancel_mono U.ι).mp
  calc
    (X.homOfLE (f.preimage_mono h) ≫ (f ∣_ U)) ≫ U.ι =
        X.homOfLE (f.preimage_mono h) ≫ ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [Category.assoc, morphismRestrict_ι]
    _ = (f ⁻¹ᵁ V).ι ≫ f := by rw [← Category.assoc, X.homOfLE_ι]
    _ = ((f ∣_ V) ≫ Y.homOfLE h) ≫ U.ι := by
      rw [Category.assoc, Y.homOfLE_ι, morphismRestrict_ι]

theorem openMatching_restrict
    (b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    {U V : Y.Opens} (h : V ≤ U)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (ha : ModuleHomTransport.Construction.moduleHomTransport U.ι a (f ∣_ U) ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) =
      ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ U).ι ((f ⁻¹ᵁ U).ι ≫ f) rfl) :
    ModuleHomTransport.Construction.moduleHomTransport V.ι (ModuleHomTransport.Construction.moduleHomTransport U.ι a (Y.homOfLE h) V.ι (Y.homOfLE_ι h))
        (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ f) (morphismRestrict_ι f V) =
      ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ V).ι ((f ⁻¹ᵁ V).ι ≫ f) rfl :=
  DescentMatching.Construction.moduleHom_matching_baseChange f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι (morphismRestrict_ι f U).symm b a ha
    (Y.homOfLE h) (X.homOfLE (f.preimage_mono h)) (f ∣_ V) (morphismRestrict_inclusion f h)
    V.ι (Y.homOfLE_ι h) (f ⁻¹ᵁ V).ι (X.homOfLE_ι (f.preimage_mono h)) (morphismRestrict_ι f V).symm

variable [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]

theorem openMatching_overlap (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (b : (Scheme.Modules.pullback f).obj L.sheaf ⟶ (Scheme.Modules.pullback f).obj M.sheaf)
    (U V : Y.Opens)
    (aU : (Scheme.Modules.pullback U.ι).obj L.sheaf ⟶ (Scheme.Modules.pullback U.ι).obj M.sheaf)
    (aV : (Scheme.Modules.pullback V.ι).obj L.sheaf ⟶ (Scheme.Modules.pullback V.ι).obj M.sheaf)
    (hU : ModuleHomTransport.Construction.moduleHomTransport U.ι aU (f ∣_ U) ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) =
      ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ U).ι ((f ⁻¹ᵁ U).ι ≫ f) rfl)
    (hV : ModuleHomTransport.Construction.moduleHomTransport V.ι aV (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ f) (morphismRestrict_ι f V) =
      ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ V).ι ((f ⁻¹ᵁ V).ι ≫ f) rfl) :
    ModuleHomTransport.Construction.moduleHomTransport U.ι aU (Y.homOfLE inf_le_left) (U ⊓ V).ι (Y.homOfLE_ι inf_le_left) =
      ModuleHomTransport.Construction.moduleHomTransport V.ι aV (Y.homOfLE inf_le_right) (U ⊓ V).ι (Y.homOfLE_ι inf_le_right) := by
  let W := U ⊓ V
  have : Surjective (f ∣_ W) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f W).flip (inferInstanceAs (Surjective f))
  have : IsAffineHom (f ∣_ W) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f W).flip (inferInstanceAs (IsAffineHom f))
  have hM : PoincareBundle.Line.Bundles.IsLine M.sheaf := M.locallyTrivial
  apply ModuleHomTransport.Construction.moduleHomTransport_injective W.ι (f ∣_ W) ((f ⁻¹ᵁ W).ι ≫ f) (morphismRestrict_ι f W)
    (FaithfulLineMorphisms.Construction.pullbackHom_injective_of_lineTarget (f ∣_ W) _ _ (hM.pullback W.ι))
  exact (openMatching_restrict f b inf_le_left aU hU).trans
    (openMatching_restrict f b inf_le_right aV hV).symm

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenDescentMatching
