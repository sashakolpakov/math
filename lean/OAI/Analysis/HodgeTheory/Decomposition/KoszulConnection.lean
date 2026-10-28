import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric
import OAI.Analysis.HodgeTheory.Decomposition.KahlerMetric

/-! # Koszul Connection -/

namespace OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions

noncomputable section

/-! The actual Koszul connection coefficient is constructed from the
inverse metric and its first derivative, with its metric and torsion identities. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def bilinearMetricSharp (B : E →L[ℝ] E →L[ℝ] ℝ) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator B).inverse.comp
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem bilinearMetricSharp_pair (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (α : E →L[ℝ] ℝ) (v : E) :
    B (bilinearMetricSharp B α) v = α v := by
  rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator_apply]
  change inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator B ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator B).inverse
    ((InnerProductSpace.toDual ℝ E).symm α))) v = α v
  rw [(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.positive_bilinear_operator_isInvertible B hpos).self_apply_inverse]
  exact InnerProductSpace.toDual_symm_apply

theorem positive_bilinear_left_ext (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) {u v : E}
    (h : ∀ w, B u w = B v w) : u = v := by
  apply (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.positive_bilinear_operator_isInvertible B hpos).injective
  apply ext_inner_right ℝ
  intro w
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator_apply, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction.realBilinearOperator_apply]
  exact h w

def koszulFirstKind (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let Tswap : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ := T.flip
  let Tcycle : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearMap.comp Tswap
  let Tsum := @Add.add (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) inferInstance T Tswap
  let Tdiff := @Sub.sub (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) inferInstance Tsum Tcycle
  (1 / 2 : ℝ) • Tdiff

theorem koszulFirstKind_apply (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    koszulFirstKind T u v w = (1 / 2 : ℝ) * (T u v w + T v u w - T w u v) := rfl

def koszulConnection (B : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (bilinearMetricSharp B)).comp (koszulFirstKind T)

theorem koszulConnection_pair (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    B (koszulConnection B T u v) w = (1 / 2 : ℝ) * (T u v w + T v u w - T w u v) :=
  bilinearMetricSharp_pair B hpos (koszulFirstKind T u v) w

theorem koszulConnection_symmetric (B : E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hS : ∀ u v w, T u v w = T u w v)
    (u v : E) : koszulConnection B T u v = koszulConnection B T v u := by
  change bilinearMetricSharp B (koszulFirstKind T u v) = bilinearMetricSharp B (koszulFirstKind T v u)
  congr 1
  ext w
  rw [koszulFirstKind_apply, koszulFirstKind_apply, hS w u v, add_comm (T u v w)]

theorem koszulConnection_metric (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hS : ∀ u v w, T u v w = T u w v)
    (u v w : E) : B (koszulConnection B T u v) w + B v (koszulConnection B T u w) = T u v w := by
  rw [hB v, koszulConnection_pair B hpos, koszulConnection_pair B hpos,
    hS u w v, hS w u v]
  ring

end

end OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions
