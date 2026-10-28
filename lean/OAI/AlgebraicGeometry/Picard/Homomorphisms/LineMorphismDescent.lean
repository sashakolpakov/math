import OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenDescentMatching
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomRestriction
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CommonLineFrames
import OAI.AlgebraicGeometry.Picard.Homomorphisms.OpenHomEquality

/-! # Line Morphism Descent -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineMorphismDescent

noncomputable section

/-! Compatible morphisms of actual pulled-back line bundles descend
uniquely. Local scalar descent and overlap matching are glued on the
base, and faithful pullback reflects the resulting isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
variable (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)

theorem existsUnique_lineHom_descent
    (b : (Scheme.Modules.pullback f).obj L.sheaf ⟶ (Scheme.Modules.pullback f).obj M.sheaf)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b ≫ (CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf).hom q x y hx hy =
        (CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf).hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b) :
    ∃! a : L.sheaf ⟶ M.sheaf, (Scheme.Modules.pullback f).map a = b := by
  classical
  let bD := ModuleHomBaseChange.Construction.canonicalDescentHom f b hb
  choose U hU e d using fun y => CommonLineFrames.Construction.common_line_frame_neighborhood L M y
  choose a ha using fun y =>
    (OpenFrameDescent.Construction.existsUnique_descent_on_frame_open f (U y) (e y).some (d y).some bD).exists
  have hmatch (i : Y) :
      ModuleHomTransport.Construction.moduleHomTransport (U i).ι (a i) (f ∣_ U i) ((f ⁻¹ᵁ U i).ι ≫ f) (morphismRestrict_ι f (U i)) =
        ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ U i).ι ((f ⁻¹ᵁ U i).ι ≫ f) rfl :=
    OpenDescentMatching.Construction.openDescentModuleHom_matches f (U i) bD b rfl (a i) (ha i)
  have hcompat (i j : Y) :
      (InternalHom.Construction.moduleInternalHom L.sheaf M.sheaf).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U i) (a i)) =
        (InternalHom.Construction.moduleInternalHom L.sheaf M.sheaf).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U j) (a j)) := by
    have h := OpenDescentMatching.Construction.openMatching_overlap f L M b (U i) (U j) (a i) (a j) (hmatch i) (hmatch j)
    exact (PullbackHomRestriction.Construction.pullbackHomOnOpenEquiv_restrict L.sheaf M.sheaf inf_le_left (a i)).symm.trans
      ((congrArg (PullbackHomGluing.Construction.pullbackHomOnOpenEquiv L.sheaf M.sheaf (U i ⊓ U j)) h).trans
        (PullbackHomRestriction.Construction.pullbackHomOnOpenEquiv_restrict L.sheaf M.sheaf inf_le_right (a j)))
  obtain ⟨a₀, ha₀, _⟩ := PullbackHomGluing.Construction.pullbackModuleHom_glue L.sheaf M.sheaf U (fun y => ⟨y, hU y⟩) a hcompat
  have hfa : (Scheme.Modules.pullback f).map a₀ = b := by
    apply OpenHomEquality.Construction.moduleHom_eq_of_open_cover (fun i => f ⁻¹ᵁ U i) (fun x => ⟨f x, hU (f x)⟩)
    intro i
    apply OpenHomEquality.Construction.moduleHomTransport_map_eq_of_eq f _ _ (f ⁻¹ᵁ U i).ι ((f ⁻¹ᵁ U i).ι ≫ f) rfl
    calc
      ModuleHomTransport.Construction.moduleHomTransport f ((Scheme.Modules.pullback f).map a₀) (f ⁻¹ᵁ U i).ι
          ((f ⁻¹ᵁ U i).ι ≫ f) rfl = (Scheme.Modules.pullback ((f ⁻¹ᵁ U i).ι ≫ f)).map a₀ :=
        OpenHomEquality.Construction.moduleHomTransport_map f a₀ _ _ _
      _ = ModuleHomTransport.Construction.moduleHomTransport (U i).ι ((Scheme.Modules.pullback (U i).ι).map a₀)
          (f ∣_ U i) ((f ⁻¹ᵁ U i).ι ≫ f) (morphismRestrict_ι f (U i)) :=
        (OpenHomEquality.Construction.moduleHomTransport_map (U i).ι a₀ _ _ _).symm
      _ = ModuleHomTransport.Construction.moduleHomTransport (U i).ι (a i) (f ∣_ U i) ((f ⁻¹ᵁ U i).ι ≫ f)
          (morphismRestrict_ι f (U i)) :=
        congrArg (fun c => ModuleHomTransport.Construction.moduleHomTransport (U i).ι c (f ∣_ U i)
          ((f ⁻¹ᵁ U i).ι ≫ f) (morphismRestrict_ι f (U i))) (ha₀ i)
      _ = ModuleHomTransport.Construction.moduleHomTransport f b (f ⁻¹ᵁ U i).ι ((f ⁻¹ᵁ U i).ι ≫ f) rfl := hmatch i
  exact ⟨a₀, hfa, fun a' ha' =>
    FaithfulLineMorphisms.Construction.pullbackHom_injective_of_lineTarget f L.sheaf M.sheaf M.locallyTrivial (ha'.trans hfa.symm)⟩

theorem exists_lineIso_of_compatible_pullbackIso
    (b : (Scheme.Modules.pullback f).obj L.sheaf ≅ (Scheme.Modules.pullback f).obj M.sheaf)
    (hb : ∀ {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X)
      (hx : x ≫ f = q) (hy : y ≫ f = q),
      (Scheme.Modules.pullback x).map b.hom ≫ (CanonicalDescentFrames.Construction.canonicalModuleDescent f M.sheaf).hom q x y hx hy =
        (CanonicalDescentFrames.Construction.canonicalModuleDescent f L.sheaf).hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b.hom) :
    ∃ e : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f).map e.hom = b.hom := by
  obtain ⟨a, ha, _⟩ := existsUnique_lineHom_descent f L M b.hom hb
  have hp : IsIso ((Scheme.Modules.pullback f).map a) := ha.symm ▸ b.isIso_hom
  have hi : IsIso a := PoincareBundle.FaithfulPullback.isIso_of_pullback f a
    L.locallyTrivial M.locallyTrivial hp
  exact ⟨asIso a, ha⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineMorphismDescent
