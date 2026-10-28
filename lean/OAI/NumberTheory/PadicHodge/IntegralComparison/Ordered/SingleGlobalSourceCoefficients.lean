import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.SingleCoefficientCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.RefinementCoefficients
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.InverseSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology

/-! # Single Global Source Coefficients -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients

noncomputable section

/-! Exact coefficient change preserves the literal common-refinement
comparison on ordered Cech cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem compose {D : Type*} [Category D]
    {A B C A' B' C' : D} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A' ⟶ B') (g' : B' ⟶ C')
    (eA : A ⟶ A') (eB : B ⟶ B') (eC : C ⟶ C')
    (hf : f ≫ eB = eA ≫ f') (hg : g ≫ eC = eB ≫ g') :
    (f ≫ g) ≫ eC = eA ≫ (f' ≫ g') := by
  rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

universe u uA vA uB vB
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]

section Refinement
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ A)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (q : ℕ)

abbrev coefficientIso :=
  OrderedCech.SingleCoefficientCoordinates.coefficientIso U (𝟭 (Cᵒᵖ ⥤ A)) G P q

omit [HasCoproducts A] [HasCoproducts B] in
theorem refinement :
    G.map (homologyMap (OrderedCech.Refinement.map U V r P) q) ≫
        (coefficientIso G P V q).hom =
      (coefficientIso G P U q).hom ≫
        homologyMap (OrderedCech.Refinement.map U V r (P ⋙ G)) q :=
  GeometricComparison.ExactHomology.ExactHomologyComparison.naturality G (.up ℕ)
    (OrderedCech.CoefficientChange.complexIso U G P)
    (OrderedCech.CoefficientChange.complexIso V G P)
    (OrderedCech.Refinement.map U V r P)
    (OrderedCech.Refinement.map U V r (P ⋙ G))
    (OrderedCech.RefinementCoefficients.complex_natural U V r G P) q

omit [HasCoproducts A] [HasCoproducts B] in
theorem refinement_isIso
    [IsIso (homologyMap (OrderedCech.Refinement.map U V r P) q)] :
    IsIso (homologyMap (OrderedCech.Refinement.map U V r (P ⋙ G)) q) :=
  Functor.InverseSquare.isIso G (coefficientIso G P U q) (coefficientIso G P V q)
    (homologyMap (OrderedCech.Refinement.map U V r P) q)
    (homologyMap (OrderedCech.Refinement.map U V r (P ⋙ G)) q)
    (refinement G P U V r q)

end Refinement

variable {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ A)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → Opens X) (V : κ → Opens X) (T : ν → Opens X)
  (rU : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι U)
  (rV : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ V)
  (q : ℕ)
  [IsIso (homologyMap (OrderedCech.Refinement.map V T rV P) q)]

omit [HasCoproducts A] [HasCoproducts B] in
theorem comparison :
    letI := refinement_isIso G P V T rV q
    G.map (SingleGlobalSource.coefficientComparison P q U V T rU rV) ≫
        (coefficientIso G P V q).hom =
      (coefficientIso G P U q).hom ≫
        SingleGlobalSource.coefficientComparison (P ⋙ G) q U V T rU rV := by
  let := refinement_isIso G P V T rV q
  have hi := Functor.InverseSquare.inverse G
    (coefficientIso G P V q) (coefficientIso G P T q)
    (homologyMap (OrderedCech.Refinement.map V T rV P) q)
    (homologyMap (OrderedCech.Refinement.map V T rV (P ⋙ G)) q)
    (refinement G P V T rV q)
  have h := compose _ _ _ _ _ _ _ (refinement G P U T rU q) hi
  simpa only [SingleGlobalSource.coefficientComparison, G.map_comp] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.SingleGlobalSourceCoefficients
