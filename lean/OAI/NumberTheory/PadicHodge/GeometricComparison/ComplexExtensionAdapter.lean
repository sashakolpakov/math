import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Adjunction

/-! # Complex Extension Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionAdapter.FormsAdapter

noncomputable section

/-! Exact coherence between extension of complexes and the actual adjunctions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits ZeroObject

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  {F : C ⥤ D} [F.Additive] {G : D ⥤ C} [G.Additive]
  (adj : F ⊣ G) {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K : HomologicalComplex C c} {L : HomologicalComplex D c}
  (φ : K ⟶ (G.mapHomologicalComplex c).obj L)

omit [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [F.Additive] [G.Additive] in
theorem adjoint_comp_id {A : C} {B : D} (f : A ⟶ G.obj B) :
    (adj.homEquiv A B).symm (f ≫ 𝟙 _) = 𝟙 _ ≫ (F.map f ≫ adj.counit.app B) := by
  rw [Category.comp_id, Category.id_comp]
  rfl

theorem adjoint_mapX (i : Option ι) :
    (adj.homEquiv (HomologicalComplex.extend.X K i) (HomologicalComplex.extend.X L i)).symm
        (HomologicalComplex.extend.mapX φ i ≫ (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso G L i).inv) =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapXIso F K i).hom ≫
        HomologicalComplex.extend.mapX
          (((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj c).homEquiv K L).symm φ) i := by
  cases i with
  | none => exact (F.map_isZero (isZero_zero C)).eq_of_src _ _
  | some i =>
    exact adjoint_comp_id adj (φ.f i)

theorem adjoint_extend (e : c.Embedding c') :
    ((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj c').homEquiv (K.extend e) (L.extend e)).symm
        (HomologicalComplex.extendMap φ e ≫ (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso G e L).inv) =
      (AlgebraicGeometry.Comparison.Betti.Complex.Extension.mapExtendIso F e K).hom ≫
        HomologicalComplex.extendMap
          (((AlgebraicGeometry.Comparison.Betti.Complex.Adjunction.onComplexes adj c).homEquiv K L).symm φ) e := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact adjoint_mapX adj φ (e.r i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexExtensionAdapter.FormsAdapter
