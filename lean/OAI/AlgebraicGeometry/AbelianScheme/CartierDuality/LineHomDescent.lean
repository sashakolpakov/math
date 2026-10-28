import OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenFrameDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CommonLineFrames
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomRestriction
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DescentMatching

/-! # Line Hom Descent -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineHomDescent.Construction.LineDescent

noncomputable section

/-!
# CartierDuality: global descent of morphisms of actual line bundles

Local framed descent is glued through the internal Hom sheaf. The
compatibility is retained on every test scheme throughout the proof.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

universe u v

/-- Morphisms of module sheaves are determined on an open cover. -/
theorem hom_ext_open_cover {X : Scheme.{u}} (L M : X.Modules)
    {ι : Type v} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (a b : L ⟶ M)
    (h : ∀ i, (Scheme.Modules.pullback (U i).ι).map a =
      (Scheme.Modules.pullback (U i).ι).map b) : a = b := by
  apply (Picard.Homomorphisms.GlobalHomSections.Construction.moduleHomGlobalSectionEquiv L M).injective
  let H := Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom L M
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨H.presheaf, H.isSheaf⟩
  apply F.eq_of_locally_eq' U ⊤ (fun i => (U i).leTop)
    (fun x _ => Opens.mem_iSup.mpr (hU x))
  intro i
  exact (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv_map L M (U i) a).symm.trans
    ((congrArg (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L M (U i)) (h i)).trans
      (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv_map L M (U i) b))

/-- Transport of a map pulled back from the base is its direct pullback. -/
theorem transport_map {X Y T : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
    (a : L ⟶ M) (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q) :
    Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f ((Scheme.Modules.pullback f).map a) t q ht =
      (Scheme.Modules.pullback q).map a := by
  rw [Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport_native]
  exact NatIso.naturality_1 (Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht) a

/-- Equality of transported maps detects equality after pullback. -/
theorem map_eq_of_transport_eq {X Y T : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}
    (a b : (Scheme.Modules.pullback f).obj L ⟶ (Scheme.Modules.pullback f).obj M)
    (t : T ⟶ X) (q : T ⟶ Y) (ht : t ≫ f = q)
    (h : Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f a t q ht = Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f b t q ht) :
    (Scheme.Modules.pullback t).map a = (Scheme.Modules.pullback t).map b := by
  let e := Scheme.Modules.pullbackComp t f ≪≫ Scheme.Modules.pullbackCongr ht
  have he : e.inv.app L ≫ (Scheme.Modules.pullback t).map a ≫ e.hom.app M =
      e.inv.app L ≫ (Scheme.Modules.pullback t).map b ≫ e.hom.app M :=
    (Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport_native f a t q ht).symm.trans
      (h.trans (Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport_native f b t q ht))
  exact (cancel_mono (e.hom.app M)).mp
    ((cancel_epi (e.inv.app L)).mp (by simpa only [Category.assoc] using he))

/-- Faithfully flat quasi-compact pullback detects line-bundle maps,
by the framed calculation on an open cover. -/
theorem pullbackHom_injective_lines {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [QuasiCompact f] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) :
    Function.Injective ((Scheme.Modules.pullback f).map : (L.sheaf ⟶ M.sheaf) → _) := by
  intro a b hab
  choose U hU e d using Picard.Homomorphisms.CommonLineFrames.Construction.common_line_frame_neighborhood L M
  apply hom_ext_open_cover L.sheaf M.sheaf U (fun y => ⟨y, hU y⟩) a b
  intro y
  have : Surjective (f ∣_ U y) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f (U y)).flip (inferInstanceAs (Surjective f))
  apply Picard.Homomorphisms.FramedModuleHomDescent.Construction.pullbackHom_injective_of_frames (f ∣_ U y) (Classical.choice (e y)) (Classical.choice (d y))
  apply map_eq_of_transport_eq (U y).ι _ _ (f ∣_ U y) ((f ⁻¹ᵁ U y).ι ≫ f)
    (morphismRestrict_ι f (U y))
  rw [transport_map, transport_map]
  rw [← transport_map f a (f ⁻¹ᵁ U y).ι ((f ⁻¹ᵁ U y).ι ≫ f) rfl,
    ← transport_map f b (f ⁻¹ᵁ U y).ι ((f ⁻¹ᵁ U y).ι ≫ f) rfl, hab]

/-- Match a descent morphism in a general commuting square before
specializing the schemes and comparison maps to open restrictions. -/
theorem square_matching {X Y U XU : Scheme.{u}}
    (f : X ⟶ Y) (g : XU ⟶ U) (s : U ⟶ Y) (t : XU ⟶ X)
    (w : t ≫ f = g ≫ s) {L M : Y.Modules}
    (b : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M)
    (a : (Scheme.Modules.pullback s).obj L ⟶ (Scheme.Modules.pullback s).obj M)
    (ha : (Scheme.Modules.pullback g).map a =
      (Picard.Homomorphisms.ModuleHomBaseChange.Construction.baseChangedDescentHom f g s t w b).hom PUnit.unit) :
    Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport s a g (t ≫ f) w.symm =
      Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) t (t ≫ f) rfl :=
  Picard.Homomorphisms.DescentMatching.Construction.moduleHom_matching_of_square f g s t w (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) a
    (ha.trans (Picard.Homomorphisms.ModuleHomBaseChange.Construction.baseChangedDescentHom_native f g s t w b))

/-- Framed descent in a commuting square supplies a matching map
without expanding the specialized open-descent object. -/
theorem exists_descent_on_square {X Y U XU : Scheme.{u}}
    (f : X ⟶ Y) (g : XU ⟶ U) (s : U ⟶ Y) (t : XU ⟶ X)
    (w : t ≫ f = g ≫ s) [Flat g] [Surjective g] [QuasiCompact g] {L M : Y.Modules}
    (e : (Scheme.Modules.pullback s).obj L ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U)
    (d : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U)
    (b : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M) :
    ∃ a : (Scheme.Modules.pullback s).obj L ⟶ (Scheme.Modules.pullback s).obj M,
      Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport s a g (t ≫ f) w.symm =
        Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) t (t ≫ f) rfl := by
  let c := Picard.Homomorphisms.ModuleHomBaseChange.Construction.baseChangedDescentHom f g s t w b
  obtain ⟨a, ha, _⟩ := Picard.Homomorphisms.FramedModuleHomDescent.Construction.existsUnique_framed_moduleHom_descent g e d (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom g c)
    (fun q x y hx hy => Picard.Homomorphisms.OpenFrameDescent.Construction.nativeDescentHom_compatible g c q x y hx hy)
  exact ⟨a, square_matching f g s t w b a ha⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L M : Y.Modules}

/-- Restricting a descended map keeps its matching equation with the cover. -/
theorem open_matching_restrict {U V : Y.Opens} (h : V ≤ U)
    (b : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L ⟶
      (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (ha : Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport U.ι a (f ∣_ U) ((f ⁻¹ᵁ U).ι ≫ f) (morphismRestrict_ι f U) =
      Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) (f ⁻¹ᵁ U).ι ((f ⁻¹ᵁ U).ι ≫ f) rfl) :
    Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport V.ι (Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport U.ι a (Y.homOfLE h) V.ι (Y.homOfLE_ι h))
        (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ f) (morphismRestrict_ι f V) =
      Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport f (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) (f ⁻¹ᵁ V).ι ((f ⁻¹ᵁ V).ι ≫ f) rfl :=
  Picard.Homomorphisms.DescentMatching.Construction.moduleHom_matching_baseChange f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι
    (morphismRestrict_ι f U).symm (Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b) a ha
    (Y.homOfLE h) (X.homOfLE (f.preimage_mono h)) (f ∣_ V)
    (morphismRestrict_homOfLE f V U h).symm V.ι (Y.homOfLE_ι h)
    (f ⁻¹ᵁ V).ι (X.homOfLE_ι (f.preimage_mono h)) (morphismRestrict_ι f V).symm

/-- Compatible morphisms of line bundles descend globally through a
faithfully flat quasi-compact cover of an arbitrary scheme. -/
theorem existsUnique_lineHom_descent [Flat f] [Surjective f] [QuasiCompact f]
    (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (b : (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj L.sheaf ⟶
      (Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj M.sheaf) :
    ∃! a : L.sheaf ⟶ M.sheaf, (Scheme.Modules.pullback f).map a = Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b := by
  choose U hU e d using Picard.Homomorphisms.CommonLineFrames.Construction.common_line_frame_neighborhood L M
  have hsurj (x : Y) : Surjective (f ∣_ U x) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f (U x)).flip (inferInstanceAs (Surjective f))
  choose a ha using fun x =>
    exists_descent_on_square f (f ∣_ U x) (U x).ι (f ⁻¹ᵁ U x).ι
      (morphismRestrict_ι f (U x)).symm (Classical.choice (e x)) (Classical.choice (d x)) b
  have hcover : ∀ y : Y, ∃ x, y ∈ U x := fun y => ⟨y, hU y⟩
  have hab : ∀ x y,
      (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom L.sheaf M.sheaf).presheaf.map
        (homOfLE (show U x ⊓ U y ≤ U x from inf_le_left)).op
        (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U x) (a x)) =
      (Picard.Homomorphisms.InternalHom.Construction.moduleInternalHom L.sheaf M.sheaf).presheaf.map
        (homOfLE (show U x ⊓ U y ≤ U y from inf_le_right)).op
        (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U y) (a y)) := by
    intro x y
    rw [← Picard.Homomorphisms.PullbackHomRestriction.Construction.pullbackHomOnOpenEquiv_restrict, ← Picard.Homomorphisms.PullbackHomRestriction.Construction.pullbackHomOnOpenEquiv_restrict]
    apply congrArg (Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U x ⊓ U y))
    let V := U x ⊓ U y
    have hs : Surjective (f ∣_ V) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f V).flip (inferInstanceAs (Surjective f))
    apply Picard.Homomorphisms.ModuleHomTransport.Construction.moduleHomTransport_injective V.ι (f ∣_ V) ((f ⁻¹ᵁ V).ι ≫ f)
      (morphismRestrict_ι f V)
      (Picard.Homomorphisms.FramedModuleHomDescent.Construction.pullbackHom_injective_of_frames (f ∣_ V)
        (L.frameRestrict inf_le_left (Classical.choice (e x)))
        (M.frameRestrict inf_le_left (Classical.choice (d x))))
    exact (open_matching_restrict f inf_le_left b (a x) (ha x)).trans
      (open_matching_restrict f inf_le_right b (a y) (ha y)).symm
  obtain ⟨a₀, ha₀, _⟩ := Picard.Homomorphisms.PullbackHomGluing.Construction.pullbackModuleHom_glue L.sheaf M.sheaf U hcover a hab
  have hfinal : (Scheme.Modules.pullback f).map a₀ = Picard.Homomorphisms.ModuleHomBaseChange.Construction.canonicalDescentModuleHom f b := by
    apply hom_ext_open_cover _ _ (fun x => f ⁻¹ᵁ U x)
      (fun z => ⟨f z, hU (f z)⟩)
    intro x
    apply map_eq_of_transport_eq f _ _ (f ⁻¹ᵁ U x).ι ((f ⁻¹ᵁ U x).ι ≫ f) rfl
    rw [transport_map]
    have hm := ha x
    rw [← ha₀ x, transport_map] at hm
    exact hm
  exact ⟨a₀, hfinal, fun a' ha' =>
    pullbackHom_injective_lines f L M (ha'.trans hfinal.symm)⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineHomDescent.Construction.LineDescent
