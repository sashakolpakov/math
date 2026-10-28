import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Complex Extension Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionNaturality.ComplexExtensionTransformation

noncomputable section

/-! The actual extension comparison is natural in additive coefficient transformations. -/

open _root_.CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (a : F ⟶ G)
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem component (K : HomologicalComplex C c) (i : Option ι) :
    a.app (HomologicalComplex.extend.X K i) ≫ (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso G K i).hom =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso F K i).hom ≫
        HomologicalComplex.extend.mapX ((NatTrans.mapHomologicalComplex a c).app K) i := by
  cases i with
  | none => exact (isZero_zero D).eq_of_tgt _ _
  | some i =>
      change a.app (K.X i) ≫ 𝟙 _ = 𝟙 _ ≫ a.app (K.X i)
      exact (Category.comp_id _).trans (Category.id_comp _).symm

theorem naturality (e : c.Embedding c') (K : HomologicalComplex C c) :
    (NatTrans.mapHomologicalComplex a c').app (K.extend e) ≫ (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G e K).hom =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F e K).hom ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex a c).app K) e := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component a K (e.r i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionNaturality.ComplexExtensionTransformation
