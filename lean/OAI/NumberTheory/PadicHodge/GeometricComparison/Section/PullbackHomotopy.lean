import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.HomotopySquare

/-! # Pullback Homotopy -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.PullbackHomotopy.SectionPullbackHomotopy

noncomputable section

/-! An injective comparison homotopy induces a homotopy of the
typed section pullback maps before any diagonal precomposition. -/

open _root_.CategoryTheory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (T : C ⥤ D) [T.Additive] (S : C ⥤ E) [S.Additive] (S' : D ⥤ E) [S'.Additive]
  (b : S ⟶ T ⋙ S') {K I : CochainComplex C ℕ} {L J : CochainComplex D ℕ}
  (c : K ⟶ I) (c' : L ⟶ J)
  (a : (T.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
  (t : (T.mapHomologicalComplex (.up ℕ)).obj I ⟶ J)
  (h : Homotopy ((T.mapHomologicalComplex (.up ℕ)).map c ≫ t) (a ≫ c'))

def homotopy : Homotopy
    ((S.mapHomologicalComplex (.up ℕ)).map c ≫ CochainPullback.SectionCochainPullback.map T S S' b t)
    (CochainPullback.SectionCochainPullback.map T S S' b a ≫ (S'.mapHomologicalComplex (.up ℕ)).map c') := by
  let h' := HomotopySquare.SectionComparisonHomotopySquare.homotopy T S S' b c c' a t
    (𝟙 _) (𝟙 _) (CochainPullback.SectionCochainPullback.map T S S' b a) h
    (by simp only [Category.id_comp, Category.comp_id, CochainPullback.SectionCochainPullback.map])
  simpa only [Category.id_comp, Category.comp_id, CochainPullback.SectionCochainPullback.map] using h'

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.PullbackHomotopy.SectionPullbackHomotopy
