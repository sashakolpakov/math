import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.Equations
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Labelled Boundary Monomial Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LabelledBoundaryMonomialTransform.Construction

noncomputable section

/-! Exact exceptional exponents for monomials in the actual labelled boundary equations. -/

universe u v

def boundaryMonomialElement {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (w : ι → R) (a : ι → ℕ) : R := ∏ j, w j ^ a j

theorem product_powers_of_exceptional_factorization
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
    (w v : ι → R) (c : R) (e a : ι → ℕ) (hw : ∀ j, w j = c ^ e j * v j) :
    (∏ j, w j ^ a j) = c ^ (∑ j, e j * a j) * ∏ j, v j ^ a j := by
  simp_rw [hw, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem boundaryMonomialElement_mixed_factorization
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I) (a : ι → ℕ) :
    Blowup.Charts.Construction.blowupChartConstants I d (boundaryMonomialElement w a) =
      Blowup.Charts.Construction.blowupChartConstants I d d.val ^ (∑ j ∈ F, a j) *
        ∏ j, MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw (some j) ^ a j := by
  classical
  rw [boundaryMonomialElement, map_prod]
  simp_rw [map_pow]
  have h := product_powers_of_exceptional_factorization (fun j => Blowup.Charts.Construction.blowupChartConstants I d (w j))
    (fun j => MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw (some j)) (Blowup.Charts.Construction.blowupChartConstants I d d.val)
    (fun j => if j ∈ F then 1 else 0) a (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily_factorization I d F w hw)
  have hsum : (∑ j, (if j ∈ F then 1 else 0) * a j) = ∑ j ∈ F, a j := by simp
  simpa only [hsum] using h

theorem boundaryMonomialElement_controlledTransform
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (d : I) (F : Finset ι) (w : ι → R) (hw : ∀ j ∈ F, w j ∈ I)
    (a : ι → ℕ) (b : ℕ) (hb : b ≤ ∑ j ∈ F, a j) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span {boundaryMonomialElement w a}) b d =
      Ideal.span {boundaryMonomialElement (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw)
        (fun j : Option ι => match j with | none => (∑ l ∈ F, a l) - b | some l => a l)} := by
  let c := Blowup.Charts.Construction.blowupChartConstants I d d.val
  let q := ∏ j, MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I d F w hw (some j) ^ a j
  have hfactor : c ^ (∑ j ∈ F, a j) * q = c ^ b * (c ^ ((∑ j ∈ F, a j) - b) * q) := by
    rw [← mul_assoc (c ^ b) (c ^ ((∑ j ∈ F, a j) - b)) q,
      ← pow_add c b ((∑ j ∈ F, a j) - b), Nat.add_sub_of_le hb]
  rw [ControlledTransform.Construction.blowupControlledTransform, Ideal.map_span, Set.image_singleton,
    boundaryMonomialElement_mixed_factorization I d F w hw a]
  change (Ideal.span {c ^ (∑ j ∈ F, a j) * q}).colon (Ideal.span {c ^ b}) = _
  rw [hfactor, ← Ideal.span_singleton_mul_span_singleton]
  have hc : IsRegular (c ^ b) := IsRegular.pow (a := c) b (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I d)
  rw [ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular (Ideal.span {c ^ ((∑ j ∈ F, a j) - b) * q}) (c ^ b) hc]
  congr 1
  rw [boundaryMonomialElement, Fintype.prod_option]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LabelledBoundaryMonomialTransform.Construction
