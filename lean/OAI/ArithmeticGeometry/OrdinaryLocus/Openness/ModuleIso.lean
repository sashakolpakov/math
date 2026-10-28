import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleLocalIso
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Module Iso -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIso.Construction

noncomputable section

/-! The open locus of local invertibility of a module morphism, and shrinking its proper base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v w w'

theorem isIso_map_of_naturalIso {C : Type u} [Category.{v} C] {D : Type w} [Category.{w'} D]
    {F G : C ⥤ D} (e : F ≅ G) {M N : C} (q : M ⟶ N) [IsIso (F.map q)] : IsIso (G.map q) := by
  have he : IsIso (e.hom.app M ≫ G.map q) := by
    rw [← e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app M) _

theorem isIso_pullbackMap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {M N : X.Modules} (q : M ⟶ N) [IsIso ((Scheme.Modules.pullback f).map q)] :
    IsIso ((Scheme.Modules.pullback (g ≫ f)).map q) := by
  have hcomp : IsIso ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback g).map q) := by
    change IsIso ((Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map q))
    infer_instance
  exact isIso_map_of_naturalIso (Scheme.Modules.pullbackComp g f) q

theorem isIso_pullbackMap_on_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    {M N : X.Modules} (q : M ⟶ N) [IsIso ((Scheme.Modules.pullback U.ι).map q)] :
    IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map ((Scheme.Modules.pullback f).map q)) := by
  have h₁ := isIso_pullbackMap_comp U.ι (f ∣_ U) q
  have h₂ : IsIso ((Scheme.Modules.pullback ((f ⁻¹ᵁ U).ι ≫ f)).map q) :=
    isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U)) q
  exact isIso_map_of_naturalIso (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).symm q

theorem isIso_pullbackMap_of_le {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N)
    (U V : X.Opens) (hVU : V ≤ U) [IsIso ((Scheme.Modules.pullback U.ι).map q)] :
    IsIso ((Scheme.Modules.pullback V.ι).map q) := by
  have h₁ := isIso_pullbackMap_comp U.ι (X.homOfLE hVU) q
  exact isIso_map_of_naturalIso (Scheme.Modules.pullbackCongr (show X.homOfLE hVU ≫ U.ι = V.ι by simp)) q

def moduleIsoLocus {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N) : X.Opens :=
  ⨆ U : {U : X.Opens // IsIso ((Scheme.Modules.pullback U.ι).map q)}, U.val

theorem mem_moduleIsoLocus_iff {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N) (x : X) :
    x ∈ moduleIsoLocus q ↔ ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.pullback U.ι).map q) := by
  constructor
  · intro hx
    obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
    exact ⟨U.val, hU, U.property⟩
  · rintro ⟨U, hx, hU⟩
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩

theorem isIso_pullback_moduleIsoLocus {X : Scheme.{u}} {M N : X.Modules} (q : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback (moduleIsoLocus q).ι).map q) := by
  apply ModuleLocalIso.Construction.isIso_of_locally_isIso_pullback
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_moduleIsoLocus_iff q x.val).mp x.property
  exact ⟨(moduleIsoLocus q).ι ⁻¹ᵁ U, hx,
    @isIso_pullbackMap_on_preimage X (moduleIsoLocus q).toScheme (moduleIsoLocus q).ι U M N q hU⟩

theorem exists_baseOpen_isIso_pullback_of_fiber_in_isoLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyClosed f] {M N : X.Modules} (q : M ⟶ N)
    (s : S) (hfiber : ∀ x : X, f x = s → x ∈ moduleIsoLocus q) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map q) := by
  let Z : Set S := f '' (moduleIsoLocus q : Set X)ᶜ
  have hZ : IsClosed Z := f.isClosedMap _ (moduleIsoLocus q).isOpen.isClosed_compl
  let U : S.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hs : s ∈ U := by
    rintro ⟨x, hx, hfx⟩
    exact hx (hfiber x hfx)
  have hU : f ⁻¹ᵁ U ≤ moduleIsoLocus q := by
    intro x hx
    by_contra hx'
    exact hx ⟨x, hx', rfl⟩
  have hi := isIso_pullback_moduleIsoLocus q
  exact ⟨U, hs, isIso_pullbackMap_of_le q (moduleIsoLocus q) (f ⁻¹ᵁ U) hU⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleIso.Construction
