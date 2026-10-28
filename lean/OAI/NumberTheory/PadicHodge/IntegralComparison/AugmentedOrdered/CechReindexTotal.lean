import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Cech Reindex Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal

noncomputable section

/-! Reindexing actual augmented ordered Čech complexes commutes
with a coefficient cochain complex and its finite totalization. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Preadditive A] [HasProducts.{u} A]

abbrev restriction : (Dᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj r.op

variable (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

def bicomplexIso :
    CechFunctor.bicomplex U (((restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≅
      CechFunctor.bicomplex (r.obj ∘ U) K :=
  (NatIso.mapHomologicalComplex (CechReindex.functorIso r U) (.up ℕ)).app K

theorem bicomplex_naturality {L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (a : K ⟶ L) :
    ((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map
      (((restriction r).mapHomologicalComplex (.up ℕ)).map a) ≫ (bicomplexIso r U L).hom =
    (bicomplexIso r U K).hom ≫
      ((CechFunctor.functor (r.obj ∘ U)).mapHomologicalComplex (.up ℕ)).map a :=
  (NatIso.mapHomologicalComplex (CechReindex.functorIso r U) (.up ℕ)).hom.naturality a

variable [HasCoproducts.{0} A]

def totalIso :
    (CechFunctor.bicomplex U
      (((restriction r).mapHomologicalComplex (.up ℕ)).obj K)).total (.up ℕ) ≅
      (CechFunctor.bicomplex (r.obj ∘ U) K).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso r U K) (.up ℕ)

theorem total_naturality {L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (a : K ⟶ L) :
    HomologicalComplex₂.total.map
      (((CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map
        (((restriction r).mapHomologicalComplex (.up ℕ)).map a)) (.up ℕ) ≫
        (totalIso r U L).hom =
    (totalIso r U K).hom ≫ HomologicalComplex₂.total.map
      (((CechFunctor.functor (r.obj ∘ U)).mapHomologicalComplex (.up ℕ)).map a) (.up ℕ) := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (bicomplex_naturality r U K a)).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechReindexTotal
