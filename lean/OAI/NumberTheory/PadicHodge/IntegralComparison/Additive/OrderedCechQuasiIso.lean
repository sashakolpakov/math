import OAI.NumberTheory.PadicHodge.IntegralComparison.Ordered.PresheafCechQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Lifted.IntegerSheaves

/-! # Ordered Cech Quasi Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechQuasiIso

noncomputable section

/-! Additive ordered Cech totals preserve quasi-isomorphisms on the
nonempty intersections, through their actual integer coefficient maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
universe u
private abbrev integral := Lifted.IntegerSheaves.coefficientForget.inv
local instance integral_additive : integral.Additive := by
  let : Lifted.IntegerSheaves.coefficientForget.asEquivalence.functor.Additive := by
    change Lifted.IntegerSheaves.coefficientForget.Additive
    infer_instance
  exact Lifted.IntegerSheaves.coefficientForget.asEquivalence.inverse_additive
local instance finiteBiproducts : HasFiniteBiproducts AddCommGrpCat.{u} :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι] (V : ι → Opens X)
  {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ} (a : K ⟶ L)

theorem quasiIso_of_evaluation
    (ha : ∀ p (j : AugmentedOrdered.Cech.Index ι (p+1)), QuasiIso
      ((((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        (op ((AugmentedOrdered.Cech.formal V (p+1)).obj j))).mapHomologicalComplex (.up ℕ)).map a)) :
    QuasiIso ((Presheaf.OrderedCover.Comparison.totalFunctor V).map a) := by
  let : QuasiIso (OrderedCech.CoefficientNaturality.Total.totalMap V
      (OrderedCech.CoefficientNaturality.Total.mappedComplexMap integral a)) := by
    apply Ordered.PresheafCechQuasiIso.quasiIso_of_evaluation Lifted.IntegerSheaves.Integers V
    intro p j
    let := ha p j
    change QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map
      ((((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        (op ((AugmentedOrdered.Cech.formal V (p+1)).obj j))).mapHomologicalComplex (.up ℕ)).map a))
    infer_instance
  have hq : QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map
      (OrderedCech.CoefficientNaturality.Total.totalMap V a) ≫
      (OrderedCech.CoefficientTotal.totalIso V integral L).hom) := by
    rw [OrderedCech.CoefficientNaturality.Total.totalIso_naturality]
    infer_instance
  have : QuasiIso ((integral.mapHomologicalComplex (.up ℕ)).map
      (OrderedCech.CoefficientNaturality.Total.totalMap V a)) :=
    quasiIso_of_comp_right _ (OrderedCech.CoefficientTotal.totalIso V integral L).hom (hφφ' := hq)
  change QuasiIso (OrderedCech.CoefficientNaturality.Total.totalMap V a)
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ integral).mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCechQuasiIso
