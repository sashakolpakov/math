import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindex

/-! # Section Reindex Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindexCoordinates

noncomputable section

/-! Atomic section and cone coordinates for reindexing an original
bounded crystalline frame family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w v' w'
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  (r : D ⥤ C) (O : C ⥤ Y.Opensᵒᵖ)

omit [Fact (Nat.Prime p)] [IsSeparated f] in
theorem section_map
    {M N : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) f n}
    (a : M ⟶ N) (d : D) :
    ((FamilySections.Family.sections f n (r ⋙ O)).map a).app d =
      ((FamilySections.Family.sections f n O).map a).app (r.obj d) := rfl

variable
  (G : C ⥤ (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (F : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
  (ρ : (Functor.const C).obj F ⟶ G)

theorem cone_app (d : D) :
    (FamilySections.Family.cone f n F
      (SectionReindex.cone f n r G F ρ)).app d =
    (FamilySections.Family.cone f n F ρ).app (r.obj d) := by
  rw [FamilySections.Family.cone_app, FamilySections.Family.cone_app]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionReindexCoordinates
