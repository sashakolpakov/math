import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap

/-! # Map Composition -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapComposition.Construction

noncomputable section

/-! The specified global blowup comparisons satisfy identity and composition by uniqueness of actual lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem globalBlowupMapTo_unique
    {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ X) (I : X.IdealSheafData) (K : Y.IdealSheafData)
    (he : I.comap q = K) (hI : I ≠ ⊥) (hK : K ≠ ⊥)
    (r : Data.Construction.globalBlowup K hK ⟶ Data.Construction.globalBlowup I hI)
    (hr : r ≫ Data.Construction.globalBlowupToBase I hI = Data.Construction.globalBlowupToBase K hK ≫ q) :
    r = SpecifiedMap.Construction.globalBlowupMapTo q I K he hI hK := by
  subst K
  exact FunctorialMap.Construction.globalBlowupMap_unique q I hI hK r hr

theorem globalBlowupMapTo_id
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I ≠ ⊥) (he : I.comap (𝟙 X) = I) :
    SpecifiedMap.Construction.globalBlowupMapTo (𝟙 X) I I he hI hI = 𝟙 (Data.Construction.globalBlowup I hI) := by
  symm
  apply globalBlowupMapTo_unique
  rw [Category.id_comp, Category.comp_id]

theorem globalBlowupMapTo_comp
    {X Y Z : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    (p : Y ⟶ X) (q : Z ⟶ Y) (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData)
    (hp : I.comap p = J) (hq : J.comap q = K) (hpq : I.comap (q ≫ p) = K)
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hK : K ≠ ⊥) :
    SpecifiedMap.Construction.globalBlowupMapTo q J K hq hJ hK ≫ SpecifiedMap.Construction.globalBlowupMapTo p I J hp hI hJ =
      SpecifiedMap.Construction.globalBlowupMapTo (q ≫ p) I K hpq hI hK := by
  apply globalBlowupMapTo_unique
  rw [Category.assoc, SpecifiedMap.Construction.globalBlowupMapTo_over, ← Category.assoc, SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.MapComposition.Construction
