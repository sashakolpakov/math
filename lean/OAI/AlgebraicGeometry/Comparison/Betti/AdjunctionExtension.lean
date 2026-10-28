import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Adjunction Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionExtension

noncomputable section

/-! Extension by zero commutes with the actual adjunction on complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem homEquiv_option {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    (g : (F.mapHomologicalComplex c).obj K ⟶ L) (o : Option ι) :
    adj.homEquiv (HomologicalComplex.extend.X K o) (HomologicalComplex.extend.X L o)
      ((Complex.Extension.mapXIso F K o).hom ≫ HomologicalComplex.extend.mapX g o) =
    HomologicalComplex.extend.mapX ((Complex.Adjunction.onComplexes adj c).homEquiv K L g) o ≫
      (Complex.Extension.mapXIso G L o).inv := by
  cases o with
  | none => exact (isZero_zero C).eq_of_src _ _
  | some i =>
    change adj.homEquiv (K.X i) (L.X i) (𝟙 _ ≫ g.f i) =
      adj.homEquiv (K.X i) (L.X i) (g.f i) ≫ 𝟙 _
    erw [Category.id_comp, Category.comp_id]

theorem homEquiv_extend (e : c.Embedding c')
    {K : HomologicalComplex C c} {L : HomologicalComplex D c}
    (g : (F.mapHomologicalComplex c).obj K ⟶ L) :
    (Complex.Adjunction.onComplexes adj c').homEquiv (K.extend e) (L.extend e)
      ((Complex.Extension.mapExtendIso F e K).hom ≫ HomologicalComplex.extendMap g e) =
    HomologicalComplex.extendMap ((Complex.Adjunction.onComplexes adj c).homEquiv K L g) e ≫
      (Complex.Extension.mapExtendIso G e L).inv := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact homEquiv_option adj g (e.r i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.AdjunctionExtension
