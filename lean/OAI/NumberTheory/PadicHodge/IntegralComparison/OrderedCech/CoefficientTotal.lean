import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientChange
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal

noncomputable section

/-! The actual nonempty ordered total and its cohomology commute with an
exact product-preserving additive coefficient functor. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

abbrev mapped := (((Functor.whiskeringRight Cᵒᵖ A B).obj G).mapHomologicalComplex (.up ℕ)).obj K

abbrev bicomplex (L : CochainComplex (Cᵒᵖ ⥤ A) ℕ) :
    HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).obj L

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (bicomplex U K) ≅ bicomplex U (mapped G K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => CoefficientChange.complexIso U G (K.X q))
    (fun q r _ => (CoefficientChange.naturality U G (K.X q) (K.d q r)).symm)

def totalIso [HasFiniteBiproducts A] :
    (G.mapHomologicalComplex (.up ℕ)).obj ((bicomplex U K).total (.up ℕ)) ≅
      (bicomplex U (mapped G K)).total (.up ℕ) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (bicomplex U K)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso U G K) (.up ℕ)

variable [HasFiniteBiproducts A] [CategoryWithHomology A] [CategoryWithHomology B]
  [G.PreservesHomology]

def homologyIso (q : ℕ) : G.obj (((bicomplex U K).total (.up ℕ)).homology q) ≅
    ((bicomplex U (mapped G K)).total (.up ℕ)).homology q :=
  ((((bicomplex U K).total (.up ℕ)).sc q).mapHomologyIso G).symm ≪≫
    homologyMapIso (totalIso U G K) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal
