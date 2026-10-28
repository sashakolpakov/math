import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Point Line Bundle Triviality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A line bundle on a nonempty scheme with a single point is globally trivial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [Subsingleton X] [Nonempty X]

theorem Line.Bundles.LineBundle.exists_trivialization_of_subsingleton (L : Line.Bundles.LineBundle X) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule X) := by
  let x : X := Nonempty.some inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim x y) ▸ hx
  subst U
  let f : (⊤ : X.Opens).toScheme ⟶ X := (⊤ : X.Opens).ι
  let : IsIso f := isIso_of_isOpenImmersion_of_opensRange_eq_top (⊤ : X.Opens).ι
    (⊤ : X.Opens).opensRange_ι
  exact ⟨(Scheme.Modules.pullbackId X).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullbackComp (inv f) f).symm.app L.sheaf ≪≫
    (Scheme.Modules.pullback (inv f)).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso (inv f)⟩

def Line.Bundles.LineBundle.trivialization_of_subsingleton (L : Line.Bundles.LineBundle X) : L.sheaf ≅ Line.Bundles.structureModule X :=
  Classical.choice L.exists_trivialization_of_subsingleton

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
