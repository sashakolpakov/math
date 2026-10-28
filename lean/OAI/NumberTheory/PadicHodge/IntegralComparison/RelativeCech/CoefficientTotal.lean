import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality

/-! # Coefficient Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientTotal

noncomputable section

/-! Coefficient transport for the literal relative Čech source, natural
in its coefficient complex. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u uA vA uB vB
variable {X : TopCat.{u}} (W : Opens X)
  {ι : Type u} [LinearOrder ι] (U : ι → Opens X)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]

local instance : HasFiniteBiproducts A := HasFiniteBiproducts.of_hasFiniteProducts

abbrev mapped (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) :=
  AugmentedCech.CoefficientTotal.mapped G K

def iso (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) :
    (G.mapHomologicalComplex (.up ℕ)).obj
        ((Total.source W U K).total (.up ℕ)) ≅
      (Total.source W U (mapped G K)).total (.up ℕ) :=
  AugmentedCech.CoefficientTotal.totalIso U G
    (((Refinement.restriction W).mapHomologicalComplex (.up ℕ)).obj K)

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ} (a : K ⟶ L) :
    (G.mapHomologicalComplex (.up ℕ)).map (Total.sourceMap W U a) ≫
        (iso W U G L).hom =
      (iso W U G K).hom ≫ Total.sourceMap W U
        (AugmentedCech.CoefficientNaturality.Total.mappedComplexMap G a) :=
  AugmentedCech.CoefficientNaturality.Total.totalIso_naturality U G
    (((Refinement.restriction W).mapHomologicalComplex (.up ℕ)).map a)

theorem quasiIso [G.PreservesHomology]
    {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ} (a : K ⟶ L)
    [QuasiIso (Total.sourceMap W U a)] :
    QuasiIso (Total.sourceMap W U
      (AugmentedCech.CoefficientNaturality.Total.mappedComplexMap G a)) := by
  have h := naturality W U G a
  rw [← Iso.inv_comp_eq] at h
  rw [← h]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CoefficientTotal
