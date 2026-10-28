import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndBaseChange

/-! # Bundle Pullback Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Unique normalization of a bundle isomorphism along a map that identifies global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem Line.Bundles.LineBundle.iso_eq_of_globalFunctions (f : Y ⟶ X) (hf : Function.Injective f.appTop)
    (L M : Line.Bundles.LineBundle X) (a b : L.sheaf ≅ M.sheaf)
    (h : (Scheme.Modules.pullback f).map a.hom = (Scheme.Modules.pullback f).map b.hom) : a = b := by
  apply Iso.ext
  apply (cancel_mono b.inv).mp
  apply Line.Bundles.LineBundle.endPullback_injective_of_globalFunctions f L hf
  change (Scheme.Modules.pullback f).map (a.hom ≫ b.inv) =
    (Scheme.Modules.pullback f).map (b.hom ≫ b.inv)
  rw [(Scheme.Modules.pullback f).map_comp, (Scheme.Modules.pullback f).map_comp, h]

theorem Line.Bundles.LineBundle.existsUnique_iso_with_pullback (f : Y ⟶ X) (hf : Function.Bijective f.appTop)
    (L M : Line.Bundles.LineBundle X) (hLM : Nonempty (L.sheaf ≅ M.sheaf))
    (b : (L.pullback f).sheaf ≅ (M.pullback f).sheaf) :
    ∃! a : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback f).map a.hom = b.hom := by
  obtain ⟨a⟩ := hLM
  let F := Scheme.Modules.pullback f
  change F.obj L.sheaf ≅ F.obj M.sheaf at b
  let ψ : End (F.obj L.sheaf) := b.hom ≫ F.map a.inv
  let q : End L.sheaf ≃+* End (F.obj L.sheaf) := Line.Bundles.LineBundle.endPullbackRingEquiv f L hf
  let φ : End L.sheaf := q.symm ψ
  have : IsIso ψ := inferInstanceAs (IsIso (b.hom ≫ F.map a.inv))
  have hψ : IsUnit ψ := (isUnit_iff_isIso ψ).mpr inferInstance
  have hφ : IsUnit φ := hψ.map q.symm.toRingHom
  let : IsIso φ := (isUnit_iff_isIso φ).mp hφ
  have hmap : F.map φ = ψ := q.apply_symm_apply ψ
  have hnorm : F.map (asIso φ ≪≫ a).hom = b.hom := by
    change F.map (φ ≫ a.hom) = b.hom
    rw [F.map_comp, hmap]
    change (b.hom ≫ F.map a.inv) ≫ F.map a.hom = b.hom
    rw [Category.assoc, ← F.map_comp, a.inv_hom_id, F.map_id, Category.comp_id]
  refine ⟨asIso φ ≪≫ a, hnorm, ?_⟩
  intro a' ha'
  exact Line.Bundles.LineBundle.iso_eq_of_globalFunctions f hf.1 L M a' (asIso φ ≪≫ a) (ha'.trans hnorm.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
