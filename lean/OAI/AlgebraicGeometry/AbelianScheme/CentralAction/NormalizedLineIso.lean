import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LineEndRigidity

/-! # Normalized Line Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedLineIso

noncomputable section

/-! Construct line-bundle isomorphisms with prescribed normalization,
using the proved correspondence between endomorphisms and global scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

/-- Surjectivity on endomorphisms corrects any existing isomorphism to
have a prescribed image; bijectivity also reflects invertibility. -/
theorem exists_iso_with_image
    {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y : C} (hF : Function.Bijective (F.mapEnd Y))
    (a : X ≅ Y) (b : F.obj X ≅ F.obj Y) :
    ∃ c : X ≅ Y, F.map c.hom = b.hom := by
  let E := MulEquiv.ofBijective (F.mapEnd Y) hF
  let d := (F.mapIso a).symm ≪≫ b
  let c : End Y := E.symm d.hom
  have hunit : IsUnit c := ((isUnit_iff_isIso d.hom).mpr d.isIso_hom).map E.symm.toMonoidHom
  have : IsIso c := (isUnit_iff_isIso c).mp hunit
  have hc : F.map c = d.hom := E.apply_symm_apply d.hom
  refine ⟨a ≪≫ asIso c, ?_⟩
  change F.map (a.hom ≫ c) = b.hom
  rw [F.map_comp, hc]
  change F.map a.hom ≫ (F.map a.inv ≫ b.hom) = b.hom
  rw [← Category.assoc, ← F.map_comp, a.hom_inv_id, F.map_id, Category.id_comp]

/-- If restriction identifies global functions, any line-bundle
isomorphism can be corrected to respect specified trivializations there. -/
theorem exists_normalized_line_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Bijective f.appTop) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (hLM : Nonempty (L.sheaf ≅ M.sheaf))
    (l : (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (m : (M.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    ∃ a : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback f).map a.hom ≫ m.hom = l.hom := by
  let F := Scheme.Modules.pullback f
  obtain ⟨a, ha⟩ := exists_iso_with_image F
    (LineEndRigidity.Construction.lineBundle_end_pullback_bijective f hf M) hLM.some (l ≪≫ m.symm)
  refine ⟨a, ?_⟩
  change F.map a.hom ≫ m.hom = l.hom
  rw [ha]
  change (l.hom ≫ m.inv) ≫ m.hom = l.hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Prescribed normalization makes that isomorphism unique. -/
theorem existsUnique_normalized_line_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Bijective f.appTop) (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y)
    (hLM : Nonempty (L.sheaf ≅ M.sheaf))
    (l : (L.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (m : (M.pullback f).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :
    ∃! a : L.sheaf ≅ M.sheaf,
      (Scheme.Modules.pullback f).map a.hom ≫ m.hom = l.hom := by
  obtain ⟨a, ha⟩ := exists_normalized_line_iso f hf L M hLM l m
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  have hab : (Scheme.Modules.pullback f).map b.hom = (Scheme.Modules.pullback f).map a.hom :=
    (cancel_mono m.hom).mp (hb.trans ha.symm)
  apply (cancel_epi a.inv).mp
  apply LineEndRigidity.Construction.lineBundle_end_pullback_injective f hf.1 M
  simp only [Functor.map_comp, hab]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.NormalizedLineIso
