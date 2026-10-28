import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal

noncomputable section

/-! The actual supported total and its cohomology commute with an
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

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (AugmentedOrdered.CechFunctor.bicomplex U K) ≅ AugmentedOrdered.CechFunctor.bicomplex U (mapped G K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => CoefficientChange.complexIso U G (K.X q))
    (fun q r _ => (CoefficientChange.naturality U G (K.X q) (K.d q r)).symm)

def totalIso [HasFiniteBiproducts A] :
    (G.mapHomologicalComplex (.up ℕ)).obj ((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)) ≅
      (AugmentedOrdered.CechFunctor.bicomplex U (mapped G K)).total (.up ℕ) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U K)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso U G K) (.up ℕ)

variable [HasFiniteBiproducts A] [CategoryWithHomology A] [CategoryWithHomology B]
  [G.PreservesHomology]

def homologyIso (q : ℕ) : G.obj (((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).homology q) ≅
    ((AugmentedOrdered.CechFunctor.bicomplex U (mapped G K)).total (.up ℕ)).homology q :=
  ((((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).sc q).mapHomologyIso G).symm ≪≫
    homologyMapIso (totalIso U G K) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal
