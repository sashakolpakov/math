import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Complex Extension Hom -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionHom.ComplexExtensionComposition

noncomputable section

/-! The actual extension comparison respects composition of additive coefficient functors. -/

open _root_.CategoryTheory Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem component (K : HomologicalComplex C c) (i : Option ι) :
    G.map (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso F K i).hom ≫
        (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso G ((F.mapHomologicalComplex c).obj K) i).hom =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso (F ⋙ G) K i).hom := by
  cases i with
  | none => exact (isZero_zero E).eq_of_tgt _ _
  | some i =>
      change G.map (𝟙 (F.obj (K.X i))) ≫ 𝟙 _ = 𝟙 _
      exact (congrArg (fun k => k ≫ 𝟙 _) (G.map_id _)).trans (Category.comp_id _)

theorem hom (e : c.Embedding c') (K : HomologicalComplex C c) :
    (G.mapHomologicalComplex c').map (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F e K).hom ≫
        (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G e ((F.mapHomologicalComplex c).obj K)).hom =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso (F ⋙ G) e K).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component F G K (e.r i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionHom.ComplexExtensionComposition
