import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

/-! # Complex Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexBaseChange

noncomputable section

/-! Precomposing a complex of presheaves with inverse image of opens
identifies its actual Čech bicomplex with the Čech bicomplex on the
inverse-image cover. The identification is natural in the complex. -/

open _root_.CategoryTheory Limits

universe w vC vD vA uC uD uA

variable {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasFiniteProducts D]
  (F : C ⥤ D) [PreservesFiniteLimits F] {ι : Type w} (U : ι → C)

def precompose : CochainComplex (Dᵒᵖ ⥤ A) ℕ ⥤ CochainComplex (Cᵒᵖ ⥤ A) ℕ :=
  ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op).mapHomologicalComplex (.up ℕ)

def bicomplexFunctor : CochainComplex (Cᵒᵖ ⥤ A) ℕ ⥤
    HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).mapHomologicalComplex (.up ℕ)

def bicomplexIso (M : CochainComplex (Dᵒᵖ ⥤ A) ℕ) :
    (bicomplexFunctor U).obj ((precompose F).obj M) ≅
      (bicomplexFunctor (F.obj ∘ U)).obj M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AlgebraicGeometry.Crystalline.Cohomology.Cech.BaseChange.CechBaseChange.complexIso F U (M.X n))
    (fun n m _ => (AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality F U (M.d n m)).symm)

theorem bicomplex_naturality {M N : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (φ : M ⟶ N) :
    (bicomplexFunctor U).map ((precompose F).map φ) ≫ (bicomplexIso F U N).hom =
      (bicomplexIso F U M).hom ≫ (bicomplexFunctor (F.obj ∘ U)).map φ := by
  ext n : 1
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.OpenBaseChangeNaturality.CechOpenBaseChangeNaturality.naturality F U (φ.f n)

variable [HasCoproducts.{0} A]

def totalIso (M : CochainComplex (Dᵒᵖ ⥤ A) ℕ) :
    ((bicomplexFunctor U).obj ((precompose F).obj M)).total (.up ℕ) ≅
      ((bicomplexFunctor (F.obj ∘ U)).obj M).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso F U M) (.up ℕ)

theorem total_naturality {M N : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (φ : M ⟶ N) :
    HomologicalComplex₂.total.map ((bicomplexFunctor U).map ((precompose F).map φ))
        (.up ℕ) ≫ (totalIso F U N).hom =
      (totalIso F U M).hom ≫
        HomologicalComplex₂.total.map ((bicomplexFunctor (F.obj ∘ U)).map φ) (.up ℕ) := by
  simpa only [totalIso, HomologicalComplex₂.total.mapIso_hom,
    ← HomologicalComplex₂.total.map_comp] using
      congrArg (fun ψ => HomologicalComplex₂.total.map ψ (.up ℕ))
        (bicomplex_naturality F U φ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexBaseChange
