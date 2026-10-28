import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves

/-! # Augmented Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechQuasiIso

noncomputable section

/-! The original additive augmented Cech total preserves maps which are
quasi-isomorphisms at every formal intersection, including the empty one. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality

private abbrev integral := Lifted.IntegerSheaves.coefficientForget.inv
local instance integral_additive : integral.Additive := by
  let : Lifted.IntegerSheaves.coefficientForget.asEquivalence.functor.Additive := by
    change Lifted.IntegerSheaves.coefficientForget.Additive
    infer_instance
  exact Lifted.IntegerSheaves.coefficientForget.asEquivalence.inverse_additive
local instance finiteBiproducts : HasFiniteBiproducts AddCommGrpCat.{u} :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ} (a : K ⟶ L)

theorem quasiIso_of_evaluation
    (ha : ∀ p (i : AugmentedOrdered.Cech.Index ι p), QuasiIso
      ((((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj
        (op ((AugmentedOrdered.Cech.formal U p).obj i))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso (AugmentedOrdered.CechForgetNaturality.map U a) := by
  let : QuasiIso (AugmentedCech.CoefficientNaturality.Total.totalMap U
      (AugmentedCech.CoefficientNaturality.Total.mappedComplexMap integral a)) := by
    apply AugmentedOrdered.CechQuasiIso.quasiIso_of_evaluation U
      Lifted.IntegerSheaves.Integers
    intro p i
    let := ha p i
    change QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map
      ((((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj
        (op ((AugmentedOrdered.Cech.formal U p).obj i))).mapHomologicalComplex (.up ℕ)).map a))
    infer_instance
  have hq : QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechForgetNaturality.map U a) ≫
      (AugmentedCech.CoefficientTotal.totalIso U integral L).hom) := by
    change QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map
      (AugmentedCech.CoefficientNaturality.Total.totalMap U a) ≫ _)
    rw [AugmentedCech.CoefficientNaturality.Total.totalIso_naturality]
    infer_instance
  have : QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map (AugmentedOrdered.CechForgetNaturality.map U a)) :=
    quasiIso_of_comp_right _ (AugmentedCech.CoefficientTotal.totalIso U integral L).hom
      (hφφ' := hq)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ integral).mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.AugmentedCechQuasiIso
