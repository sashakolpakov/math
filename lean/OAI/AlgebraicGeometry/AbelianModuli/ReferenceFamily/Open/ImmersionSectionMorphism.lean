import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionGlobalSections

/-! # Immersion Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionSectionMorphism

noncomputable section

/-! The original global-section isomorphisms on open immersions
commute with a morphism between the ambient schemes and an actual
commuting map between their affine presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem schemeAppLE_congrMap {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem openImmersionTopSectionIso_morphism {X Y A B : Scheme.{0}}
    (f : X ⟶ Y) (i : Y ⟶ B) (j : X ⟶ A) (g : A ⟶ B)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hf : f ≫ i = j ≫ g) (h : j.opensRange ≤ g ⁻¹ᵁ i.opensRange) :
    f.appTop ≫ (IsOpenImmersion.ΓIsoTop j).hom =
      (IsOpenImmersion.ΓIsoTop i).hom ≫ g.appLE i.opensRange j.opensRange h := by
  apply (cancel_epi (IsOpenImmersion.ΓIsoTop i).inv).mp
  apply (cancel_mono (IsOpenImmersion.ΓIsoTop j).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  have ei : (⊤ : Y.Opens) ≤ i ⁻¹ᵁ i.opensRange := by rw [i.preimage_opensRange]
  have ef : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := le_top
  have ej : (⊤ : X.Opens) ≤ j ⁻¹ᵁ j.opensRange := by rw [j.preimage_opensRange]
  have ht : f.appTop = f.appLE ⊤ ⊤ ef := (f.appLE_eq_app (U := ⊤)).symm
  calc
    (IsOpenImmersion.ΓIsoTop i).inv ≫ f.appTop = i.appLE i.opensRange ⊤ ei ≫ f.appLE ⊤ ⊤ ef :=
      congrArg₂ (· ≫ ·) (ImmersionGlobalSections.openImmersionTopSectionIso_inv i) ht
    _ = (f ≫ i).appLE i.opensRange ⊤
        (ef.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE ei)).le) :=
      Scheme.Hom.appLE_comp_appLE f i i.opensRange ⊤ ⊤ ei ef
    _ = (j ≫ g).appLE i.opensRange ⊤
        (ej.trans ((TopologicalSpace.Opens.map j.base).map (homOfLE h)).le) :=
      schemeAppLE_congrMap hf i.opensRange ⊤ _ _
    _ = g.appLE i.opensRange j.opensRange h ≫ j.appLE j.opensRange ⊤ ej :=
      (Scheme.Hom.appLE_comp_appLE j g i.opensRange j.opensRange ⊤ h ej).symm
    _ = g.appLE i.opensRange j.opensRange h ≫ (IsOpenImmersion.ΓIsoTop j).inv :=
      congrArg (fun t => g.appLE i.opensRange j.opensRange h ≫ t) (ImmersionGlobalSections.openImmersionTopSectionIso_inv j).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionSectionMorphism
