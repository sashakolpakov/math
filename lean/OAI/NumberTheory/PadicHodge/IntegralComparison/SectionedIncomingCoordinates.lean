import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingHomotopy

/-! # Sectioned Incoming Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingCoordinates

noncomputable section

/-! Pointwise coordinates for a sectioned incoming comparison. -/

open _root_.CategoryTheory

universe u v w a b c d e
variable {A : Type u} [Category.{a} A] [Preadditive A]
  {B : Type v} [Category.{b} B] [Preadditive B]
  {C : Type w} [Category.{c} C] [Preadditive C]
  {D : Type d} [Category.{e} D]
  (R : A ⥤ B) [R.Additive] (S : A ⥤ D ⥤ C) [S.Additive]
  (T : B ⥤ D ⥤ C) [T.Additive] (e : S ≅ R ⋙ T)
  {K L : CochainComplex A ℕ}
  (b : (R.mapHomologicalComplex (.up ℕ)).obj K ⟶
    (R.mapHomologicalComplex (.up ℕ)).obj L)

theorem component (q : ℕ) (d : D) :
    ((SectionedIncomingHomotopy.map R S T e b).f q).app d =
      (e.hom.app (K.X q)).app d ≫ (T.map (b.f q)).app d ≫
        (e.inv.app (L.X q)).app d := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SectionedIncomingCoordinates
