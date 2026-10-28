import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineOpen.QuasicoherentLocalization
import Mathlib.RingTheory.Flat.Localization

/-! # Affine Sections Flat -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.AffineSectionsFlat

noncomputable section

/-! Sections of an actual HilbertConstruction line bundle on any affine open form a flat module over its section ring. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules
universe u

def overFrameSectionsIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
  ((PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

theorem lineBundle_affineOpen_sections_flat {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (U : X.affineOpens) :
    Module.Flat Γ(X, U.1) Γ(L.sheaf, U.1) := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  choose V hx hv using L.locallyTrivial
  have hV : ⨆ x : X, V x = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let t : Set Γ(X, U.1) := {f | ∃ i : X, X.basicOpen f ≤ V i}
  have hopen : ⨆ f : t, X.basicOpen f.1 = U.1 := by
    apply le_antisymm
    · exact iSup_le fun f => X.basicOpen_le f.1
    · calc
        U.1 = U.1 ⊓ ⊤ := by simp
        _ = U.1 ⊓ ⨆ i, V i := by rw [hV]
        _ = ⨆ i, U.1 ⊓ V i := by rw [inf_iSup_eq]
        _ ≤ ⨆ f : t, X.basicOpen f.1 := by
          refine iSup_le fun i => ?_
          rintro x hx
          obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hx.2⟩ hx.1
          have hle : X.basicOpen f ≤ ⨆ g : t, X.basicOpen g.1 :=
            le_iSup_of_le (⟨f, i, hf⟩ : t) le_rfl
          exact hle hxf
  have ht : Ideal.span t = ⊤ := U.2.iSup_basicOpen_eq_self_iff.mp hopen
  let (g : t) : Algebra Γ(X, U.1) Γ(X, X.basicOpen g.1) := inferInstance
  let (g : t) : Module Γ(X, U.1) Γ(L.sheaf, X.basicOpen g.1) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(X, X.basicOpen g.1))
  let (g : t) : IsLocalization.Away g.1 Γ(X, X.basicOpen g.1) := U.2.isLocalization_basicOpen g.1
  let (g : t) : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen g.1) Γ(L.sheaf, X.basicOpen g.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let φ : (g : t) → Γ(L.sheaf, U.1) →ₗ[Γ(X, U.1)] Γ(L.sheaf, X.basicOpen g.1) := fun g => {
    toFun := L.sheaf.presheaf.map (homOfLE (X.basicOpen_le g.1)).op
    map_add' := (L.sheaf.presheaf.map (homOfLE (X.basicOpen_le g.1)).op).hom.map_add
    map_smul' := fun r x => L.sheaf.map_smul (homOfLE (X.basicOpen_le g.1)) r x }
  have : ∀ g : t, IsLocalizedModule.Away g.1 (φ g) := fun g =>
    AffineOpen.QuasicoherentLocalization.affineOpen_quasicoherent_sections_localize L.sheaf U g.1
  apply Module.flat_of_isLocalized_span Γ(X, U.1) Γ(L.sheaf, U.1) t ht
    (fun g => Γ(L.sheaf, X.basicOpen g.1)) φ
  intro g
  obtain ⟨i, hi⟩ := g.property
  obtain ⟨e⟩ := hv i
  let e' := L.overFrameIso (X.basicOpen g.1) (L.frameRestrict hi e)
  have : Module.Flat Γ(X, X.basicOpen g.1) Γ(L.sheaf, X.basicOpen g.1) :=
    Module.Flat.of_linearEquiv (overFrameSectionsIso L.sheaf _ e')
  have : Module.Flat Γ(X, U.1) Γ(X, X.basicOpen g.1) :=
    IsLocalization.flat _ (Submonoid.powers g.1)
  exact Module.Flat.trans Γ(X, U.1) Γ(X, X.basicOpen g.1) Γ(L.sheaf, X.basicOpen g.1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.AffineSectionsFlat
