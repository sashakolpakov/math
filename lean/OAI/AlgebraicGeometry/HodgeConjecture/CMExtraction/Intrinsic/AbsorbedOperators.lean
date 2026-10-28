import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.NeighborOperators
import OAI.NumberTheory.PadicHodge.IntrinsicModel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Realization

/-! # Absorbed Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedOperators

noncomputable section

/-! Identify FrobeniusSlope's absorbed operators and their integral realizations
with NeighborCounting's original raw ordinary-neighbor types. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EndomorphismComparison.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ComparisonAction.CM
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)

include hA in
theorem native_absorbed_eq_neighbor (side : Fin s → Bool) (i : Fin 3) :
    NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i =
      A.basis (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i).val := by
  have ht := MinusculeParameters.nativeMinusculeHecke_three D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) hg hq hIsogenyQuotient
    (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection_realizes D hg hq hIsogenyQuotient A hA)
  have h := NeighborOperators.native_neighbor_raw_basis A.basis hA.raw D.reference.distinguished side i
  fin_cases i
  · change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished side *
      MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1 = _
    change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished side ^ 1 *
      A.basis (MinusculeParameters.activeMinusculeType D.reference.distinguished 1) = _ at h
    rw [pow_one] at h
    exact h
  · exact h
  · change AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished side ^ 3 * AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished = _
    rw [← ht]
    exact h

theorem native_realization_integral
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q) (t : AbelianScheme.TateComparison.Local.IntegralType s) :
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j).action (A.basis t.val) =
      (1 : ℚ) ⊗ₜ[ℤ] HeckeCycles.EndomorphismComparison.CM.integralEquiv (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).variety.scheme (A.TAlb t) := by
  exact HeckeCycles.Realization.CM.RawHecke.action_on_integral_operator (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) A.rho
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j)
    (HeckeCycles.Intrinsic.ComparisonAction.CM.native_hecke_realization D hg j hq.2.2.2.1 A.rho A.rhoH1 hA.cohomology).choose_spec.1
    (A.basis t.val) (A.TAlb t) (hA.integral t)

theorem native_absorbed_integral
    (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q) (side : Fin s → Bool) (i : Fin 3) :
    (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j).action (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i) =
      (1 : ℚ) ⊗ₜ[ℤ] HeckeCycles.EndomorphismComparison.CM.integralEquiv (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).variety.scheme
        (A.TAlb (HeckeCycles.Neighbor.Types.CM.integralType D.reference.distinguished side i)) := by
  rw [native_absorbed_eq_neighbor D hg hq hIsogenyQuotient A hA]
  exact native_realization_integral D hg hq hIsogenyQuotient A hA j _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.AbsorbedOperators
