import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Complex Whisker -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexWhisker.SectionComplexWhisker

noncomputable section

/-! Reindexing a complex diagram and composing its section functor
preserves the actual section-comparison transformation. -/

open _root_.CategoryTheory

variable {C C' A B D D' : Type*}
  [Category* C] [Category* C'] [Category* A] [Category* B] [Category* D] [Category* D']
  [Preadditive A] [Preadditive B] [Preadditive D] [Preadditive D']
  (T : A ⥤ B) [T.Additive] (S : A ⥤ D) [S.Additive] (S' : B ⥤ D) [S'.Additive]
  (P : C ⥤ CochainComplex A ℕ) (Q : C ⥤ CochainComplex B ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')
  (V : C' ⥤ C) (H : D ⥤ D') [H.Additive]

theorem natural :
    Functor.whiskerRight (Functor.whiskerLeft V
      (Functor.whiskerLeft P (b.mapHomologicalComplex (.up ℕ)) ≫
        Functor.whiskerRight a (S'.mapHomologicalComplex (.up ℕ)))) (H.mapHomologicalComplex (.up ℕ)) =
    Functor.whiskerLeft (V ⋙ P) ((Functor.whiskerRight b H).mapHomologicalComplex (.up ℕ)) ≫
      Functor.whiskerRight (Functor.whiskerLeft V a) ((S' ⋙ H).mapHomologicalComplex (.up ℕ)) := by
  apply NatTrans.ext
  funext X
  apply HomologicalComplex.Hom.ext
  funext i
  exact H.map_comp _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexWhisker.SectionComplexWhisker
