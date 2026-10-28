import OAI.AlgebraicGeometry.CycleClass.Thom.GlobalSectionUnitEvaluation

/-! # Section Basic -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions.Pullback

/-! Sections on an actual open subscheme pull back by the same ring map
as their original ambient sections restricted along the commuting map. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Z : Scheme} (B : Z.Opens)

theorem openInclusion_appLE_self (h : (⊤ : B.toScheme.Opens) ≤ B.ι ⁻¹ᵁ B) :
    B.ι.appLE B ⊤ h = B.topIso.inv := by
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

theorem appLE_open_factor (g : X ⟶ B.toScheme) (i : X ⟶ Z) (hi : g ≫ B.ι = i)
    (hB : (⊤ : X.Opens) ≤ i ⁻¹ᵁ B) :
    B.topIso.hom ≫ i.appLE B ⊤ hB = g.appTop := by
  subst i
  have hb : (⊤ : B.toScheme.Opens) ≤ B.ι ⁻¹ᵁ B := by rw [B.ι_preimage_self]
  have h := Scheme.Hom.appLE_comp_appLE g B.ι B ⊤ ⊤ hb (show (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)
  rw [openInclusion_appLE_self] at h
  have hg : g.appLE ⊤ ⊤ le_top = g.appTop := g.app_eq_appLE.symm
  have he : B.topIso.inv ≫ g.appTop = (g ≫ B.ι).appLE B ⊤ hB :=
    (congrArg (fun k => B.topIso.inv ≫ k) hg.symm).trans h
  calc
    B.topIso.hom ≫ (g ≫ B.ι).appLE B ⊤ hB = B.topIso.hom ≫ (B.topIso.inv ≫ g.appTop) :=
      congrArg (fun k => B.topIso.hom ≫ k) he.symm
    _ = g.appTop := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem appLE_open_factor_apply (g : X ⟶ B.toScheme) (i : X ⟶ Z) (hi : g ≫ B.ι = i)
    (hB : (⊤ : X.Opens) ≤ i ⁻¹ᵁ B) (s : Γ(B.toScheme, ⊤)) :
    i.appLE B ⊤ hB (B.topIso.hom s) = g.appTop s :=
  ConcreteCategory.congr_hom (appLE_open_factor B g i hi hB) s

end AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions.Pullback

namespace AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions

/-! The zero and unit loci of a section on an open subscheme are the
same loci in the original ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {X : Scheme} (B : X.Opens) (s : Γ(B.toScheme, ⊤))

 theorem openSection_basicOpen_image :
    B.ι ''ᵁ B.toScheme.basicOpen s = X.basicOpen (B.topIso.hom s) := by
  simpa only [Iso.hom_inv_id_apply] using B.ι_image_basicOpen_topIso_inv (B.topIso.hom s)

 theorem openSection_mem_basicOpen_image (x : B.toScheme) (hx : x ∈ B.toScheme.basicOpen s) :
    B.ι x ∈ X.basicOpen (B.topIso.hom s) := by
  rw [← openSection_basicOpen_image B s]
  exact ⟨x, hx, rfl⟩

end AlgebraicGeometry.CycleClass.Thom.Open.SectionBasic.Constructions

end

end OAI
