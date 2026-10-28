import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientForget
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.TotalCoefficientSquare

/-! # Refinement Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCoefficientTotal

noncomputable section

/-! Actual ordered and augmented cover refinements commute with coefficient
transport on their original total complexes and homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coefficient_homology_square
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (G : A ⥤ B) [G.Additive] [G.PreservesHomology]
    {K L : CochainComplex A ℕ} {K' L' : CochainComplex B ℕ}
    (eK : (G.mapHomologicalComplex (.up ℕ)).obj K ≅ K')
    (eL : (G.mapHomologicalComplex (.up ℕ)).obj L ≅ L')
    (f : K ⟶ L) (g : K' ⟶ L')
    (h : (G.mapHomologicalComplex (.up ℕ)).map f ≫ eL.hom = eK.hom ≫ g) (q : ℕ) :
    G.map (homologyMap f q) ≫ (((L.sc q).mapHomologyIso G).symm ≪≫ homologyMapIso eL q).hom =
      (((K.sc q).mapHomologyIso G).symm ≪≫ homologyMapIso eK q).hom ≫ homologyMap g q := by
  have ht := congrArg (fun a => homologyMap a q) h
  simp only [homologyMap_comp] at ht
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor A (.up ℕ) q).map f) G
  change G.map (homologyMap f q) ≫ ((L.sc q).mapHomologyIso G).inv =
    ((K.sc q).mapHomologyIso G).inv ≫ homologyMap ((G.mapHomologicalComplex (.up ℕ)).map f) q at hn
  change G.map (homologyMap f q) ≫ (((L.sc q).mapHomologyIso G).inv ≫ homologyMap eL.hom q) =
    (((K.sc q).mapHomologyIso G).inv ≫ homologyMap eK.hom q) ≫ homologyMap g q
  rw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc]

universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

namespace OrderedCechRefinementCoefficients
open OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientTotal

omit [HasFiniteBiproducts A] [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplex_natural :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (OrderedCech.Refinement.bicomplexMap U V r K) ≫
        (OrderedCech.CoefficientTotal.bicomplexIso V G K).hom =
      (OrderedCech.CoefficientTotal.bicomplexIso U G K).hom ≫
        OrderedCech.Refinement.bicomplexMap U V r (OrderedCech.CoefficientTotal.mapped G K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact OrderedCech.RefinementCoefficients.complex_natural U V r G (K.X n)

theorem total_natural :
    (G.mapHomologicalComplex (.up ℕ)).map (OrderedCech.Refinement.totalMap U V r K) ≫
        (OrderedCech.CoefficientTotal.totalIso V G K).hom =
      (OrderedCech.CoefficientTotal.totalIso U G K).hom ≫ OrderedCech.Refinement.totalMap U V r (OrderedCech.CoefficientTotal.mapped G K) :=
  Finite.TotalCoefficientSquare.comparison G (OrderedCech.CoefficientTotal.bicomplexIso U G K) (OrderedCech.CoefficientTotal.bicomplexIso V G K)
    (OrderedCech.Refinement.bicomplexMap U V r K)
    (OrderedCech.Refinement.bicomplexMap U V r (OrderedCech.CoefficientTotal.mapped G K))
    (bicomplex_natural U V r G K)

theorem homology_natural [G.PreservesHomology] (q : ℕ) :
    G.map (homologyMap (OrderedCech.Refinement.totalMap U V r K) q) ≫
        (OrderedCech.CoefficientTotal.homologyIso V G K q).hom =
      (OrderedCech.CoefficientTotal.homologyIso U G K q).hom ≫
        homologyMap (OrderedCech.Refinement.totalMap U V r (OrderedCech.CoefficientTotal.mapped G K)) q :=
  coefficient_homology_square G (OrderedCech.CoefficientTotal.totalIso U G K) (OrderedCech.CoefficientTotal.totalIso V G K)
    (OrderedCech.Refinement.totalMap U V r K)
    (OrderedCech.Refinement.totalMap U V r (OrderedCech.CoefficientTotal.mapped G K))
    (total_natural U V r G K) q

end OrderedCechRefinementCoefficients

namespace AugmentedCechRefinementCoefficients

omit [HasFiniteBiproducts A] in
omit [HasCoproducts A] [HasCoproducts B] in
theorem complex_natural (P : Cᵒᵖ ⥤ A) :
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechRefinement.map U V r P) ≫
        (AugmentedCech.CoefficientChange.complexIso V G P).hom =
      (AugmentedCech.CoefficientChange.complexIso U G P).hom ≫
        AugmentedOrdered.CechRefinement.map U V r (P ⋙ G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
    change G.map ((AugmentedOrdered.CechZero.zeroIso U P).hom ≫ (AugmentedOrdered.CechZero.zeroIso V P).inv) ≫
        (AugmentedCech.CoefficientChange.objectIso V G P 0).hom =
      (AugmentedCech.CoefficientChange.objectIso U G P 0).hom ≫
        ((AugmentedOrdered.CechZero.zeroIso U (P ⋙ G)).hom ≫ (AugmentedOrdered.CechZero.zeroIso V (P ⋙ G)).inv)
    apply (cancel_mono (AugmentedOrdered.CechZero.zeroIso V (P ⋙ G)).hom).mp
    simp only [G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [AugmentedCech.CoefficientForget.zero,
      ← G.map_comp (AugmentedOrdered.CechZero.zeroIso V P).inv (AugmentedOrdered.CechZero.zeroIso V P).hom,
      Iso.inv_hom_id, G.map_id, Category.comp_id,
      AugmentedCech.CoefficientForget.zero]
  | succ n =>
    exact congrArg (fun a => a.f n)
      (OrderedCech.RefinementCoefficients.complex_natural U V r G P)

omit [HasFiniteBiproducts A] in
omit [HasCoproducts A] [HasCoproducts B] in
theorem bicomplex_natural :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r K) ≫
        (AugmentedCech.CoefficientTotal.bicomplexIso V G K).hom =
      (AugmentedCech.CoefficientTotal.bicomplexIso U G K).hom ≫
        AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r (AugmentedCech.CoefficientTotal.mapped G K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact complex_natural U V r G (K.X n)

theorem total_natural :
    (G.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechRefinementTotal.totalMap U V r K) ≫
        (AugmentedCech.CoefficientTotal.totalIso V G K).hom =
      (AugmentedCech.CoefficientTotal.totalIso U G K).hom ≫ AugmentedOrdered.CechRefinementTotal.totalMap U V r (AugmentedCech.CoefficientTotal.mapped G K) :=
  Finite.TotalCoefficientSquare.comparison G (AugmentedCech.CoefficientTotal.bicomplexIso U G K) (AugmentedCech.CoefficientTotal.bicomplexIso V G K)
    (AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r K)
    (AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r (AugmentedCech.CoefficientTotal.mapped G K))
    (bicomplex_natural U V r G K)

theorem homology_natural [G.PreservesHomology] (q : ℕ) :
    G.map (homologyMap (AugmentedOrdered.CechRefinementTotal.totalMap U V r K) q) ≫
        (AugmentedCech.CoefficientTotal.homologyIso V G K q).hom =
      (AugmentedCech.CoefficientTotal.homologyIso U G K q).hom ≫
        homologyMap (AugmentedOrdered.CechRefinementTotal.totalMap U V r (AugmentedCech.CoefficientTotal.mapped G K)) q :=
  coefficient_homology_square G (AugmentedCech.CoefficientTotal.totalIso U G K) (AugmentedCech.CoefficientTotal.totalIso V G K)
    (AugmentedOrdered.CechRefinementTotal.totalMap U V r K)
    (AugmentedOrdered.CechRefinementTotal.totalMap U V r (AugmentedCech.CoefficientTotal.mapped G K))
    (total_natural U V r G K) q

end AugmentedCechRefinementCoefficients

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementCoefficientTotal
