import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.MonomialTransform

/-! # Residual Boundary Monomial Update -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ResidualBoundaryMonomialUpdate.Construction

noncomputable section

/-! The canonical residual factor update preserves an exact global labelled boundary monomial. -/

universe u v

def residualBoundaryMonomialExponents {ι : Type v} (F : Finset ι) (a : ι → ℕ) (m b : ℕ) :
    Option ι → ℕ
  | none => (m - b) + ((∑ j ∈ F, a j) - (b - m))
  | some j => a j

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem residualBoundaryFactorTransform_monomial
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (a : ι → ℕ) (m b : ℕ) (hM : Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a} ≤ I ^ (b - m))
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I d)) (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)) :
    ResidualCoefficientTransform.Construction.residualBoundaryFactorTransform I (Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement w a}) d m b =
      Ideal.span {LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)
        (residualBoundaryMonomialExponents F a m b)} := by
  rw [ResidualCoefficientTransform.Construction.residualBoundaryFactorTransform,
    Boundary.MonomialTransform.Construction.boundaryMonomialElement_controlledTransform_of_boundary R I d F w hw a (b - m) hM hboundary,
    Ideal.span_singleton_mul_span_singleton]
  apply congrArg (fun x : Blowup.Charts.Construction.blowupChart I d => Ideal.span {x})
  rw [LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, Fintype.prod_option, LabelledBoundaryMonomialTransform.Construction.boundaryMonomialElement, Fintype.prod_option]
  let c := Blowup.Charts.Construction.blowupChartConstants I d d.val
  let q := ∏ j, MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw (some j) ^ a j
  change c ^ (m - b) * (c ^ ((∑ j ∈ F, a j) - (b - m)) * q) =
    c ^ ((m - b) + ((∑ j ∈ F, a j) - (b - m))) * q
  rw [← mul_assoc (c ^ (m - b)) (c ^ ((∑ j ∈ F, a j) - (b - m))) q,
    ← pow_add c (m - b) ((∑ j ∈ F, a j) - (b - m))]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ResidualBoundaryMonomialUpdate.Construction
