import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Immersion Global Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections

noncomputable section

section

/-! The canonical sections isomorphism of an open immersion commutes
with an actual map between open subfamilies of the same ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openImmersionTopSectionIso_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE f.opensRange ⊤ (by rw [f.preimage_opensRange]) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv,
    eqToIso.inv, eqToHom_op, Iso.symm_inv, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

theorem openImmersionTopSectionIso_natural {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) (i : Y ⟶ Z) (j : X ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (hf : f ≫ i = j) (h : j.opensRange ≤ i.opensRange) :
    f.appTop ≫ (IsOpenImmersion.ΓIsoTop j).hom =
      (IsOpenImmersion.ΓIsoTop i).hom ≫ Z.presheaf.map (homOfLE h).op := by
  apply (cancel_epi (IsOpenImmersion.ΓIsoTop i).inv).mp
  apply (cancel_mono (IsOpenImmersion.ΓIsoTop j).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have ei : (⊤ : Y.Opens) ≤ i ⁻¹ᵁ i.opensRange := by rw [i.preimage_opensRange]
  have ef : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  have ej : (⊤ : X.Opens) ≤ j ⁻¹ᵁ j.opensRange := by rw [j.preimage_opensRange]
  have ej' : (⊤ : X.Opens) ≤ j ⁻¹ᵁ i.opensRange := ej.trans (j.preimage_mono h)
  have ht : f.appTop = f.appLE ⊤ ⊤ ef := (f.appLE_eq_app (U := ⊤)).symm
  calc
    (IsOpenImmersion.ΓIsoTop i).inv ≫ f.appTop = i.appLE i.opensRange ⊤ ei ≫ f.appLE ⊤ ⊤ ef :=
      congrArg₂ (· ≫ ·) (openImmersionTopSectionIso_inv i) ht
    _ = (f ≫ i).appLE i.opensRange ⊤ (ef.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE ei)).le) :=
      Scheme.Hom.appLE_comp_appLE f i i.opensRange ⊤ ⊤ ei ef
    _ = j.appLE i.opensRange ⊤ ej' := by subst j; rfl
    _ = Z.presheaf.map (homOfLE h).op ≫ j.appLE j.opensRange ⊤ ej :=
      (j.map_appLE ej (homOfLE h).op).symm
    _ = Z.presheaf.map (homOfLE h).op ≫ (IsOpenImmersion.ΓIsoTop j).inv :=
      congrArg (fun q => Z.presheaf.map (homOfLE h).op ≫ q) (openImmersionTopSectionIso_inv j).symm

end

/-! The actual global-section isomorphism of an open immersion
sends pullbacks of global functions to their ordinary restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem openImmersionTopSection_global {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    (s : Γ(Y, ⊤)) :
    (IsOpenImmersion.ΓIsoTop f).hom (f.appTop s) =
      Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op s := by
  have ef : (⊤ : X.Opens) ≤ f ⁻¹ᵁ f.opensRange := by rw [f.preimage_opensRange]
  have h : Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op ≫
      (IsOpenImmersion.ΓIsoTop f).inv = f.appTop := by
    calc
      _ = Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op ≫ f.appLE f.opensRange ⊤ ef :=
        congrArg (fun q => Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op ≫ q)
          (openImmersionTopSectionIso_inv f)
      _ = f.appLE ⊤ ⊤ (ef.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE le_top)).le) :=
        f.map_appLE ef (homOfLE le_top).op
      _ = f.appTop := f.appLE_eq_app
  have he : f.appTop ≫ (IsOpenImmersion.ΓIsoTop f).hom =
      Y.presheaf.map (homOfLE (show f.opensRange ≤ ⊤ from le_top)).op := by
    apply (cancel_mono (IsOpenImmersion.ΓIsoTop f).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact h.symm
  exact ConcreteCategory.congr_hom he s

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections
