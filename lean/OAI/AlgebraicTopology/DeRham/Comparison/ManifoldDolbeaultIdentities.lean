import OAI.AlgebraicTopology.DeRham.Comparison.DolbeaultSecondSum
import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeIndependence
import OAI.AlgebraicTopology.DeRham.Comparison.IncomingDerivativeTransport

/-! # Manifold Dolbeault Identities -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities.PureManifoldForm

noncomputable section

/-!
# Square-zero identities and actual exactness of the Clay denominator

The three full bidegree characters in the second derivative are independent.
Consequently `d² = 0` gives the two square-zero identities and the mixed
anticommutation identity. In particular, the literal `d' d''` of a pure form
is the actual exterior derivative of its `d''`, so it is a closed exact form.
-/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {p q : ℕ}

/-- The three actual bidegree pieces of the second exterior derivative vanish separately. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_parts_zero (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) = 0 ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form) = 0 ∧
      Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form) = 0 := by
  let A : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 2) :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : ((p + 1) + 1) + q = p + q + 2)
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).1
  let B : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 2) :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : (p + 1) + (q + 1) = p + q + 2)
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1
  let C : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 2) :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree (by omega : p + ((q + 1) + 1) = p + q + 2)
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1
  have hsum : A + B + C = 0 := by
    dsimp only [A, B, C]
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree _ (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).1 +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree _
        ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).1 + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1) +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree _ (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).1 = 0
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_add]
    convert Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_sum form using 1
    abel
  have hA : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (A : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 2) q z⁻¹ • (A : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) := by
    intro z
    dsimp only [A]
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_coe]
    exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form)).hasManifoldBidegree.complexAction_castDegree _ z
  have hB : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (B : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (p + 1) (q + 1) z⁻¹ • (B : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) := by
    intro z
    dsimp only [B]
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_coe]
    exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.complexAction_castDegree
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).hasManifoldBidegree _ z
  have hC : ∀ z : ℂˣ, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.complexAction z (C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p (q + 2) z⁻¹ • (C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) := by
    intro z
    dsimp only [C]
    rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_coe]
    exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form)).hasManifoldBidegree.complexAction_castDegree _ z
  have hsumRaw : (A : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) +
      (B : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) + (C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) = 0 :=
    congrArg (fun s : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q + 2) =>
      (s : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2))) hsum
  obtain ⟨ha, hb, hc⟩ := BidegreeIndependence.rawManifoldForm_neighbor_triple_eq_zero
    (A : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) (B : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2))
    (C : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q + 2)) hA hB hC hsumRaw
  have ha' : A = 0 := Subtype.ext ha
  have hb' : B = 0 := Subtype.ext hb
  have hc' : C = 0 := Subtype.ext hc
  refine ⟨?_, ?_, ?_⟩
  · apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_eq_zero_iff _ _).mp ha'
  · apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_eq_zero_iff _ _).mp hb'
  · apply Subtype.ext
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_eq_zero_iff _ _).mp hc'

/-- The actual global holomorphic differential squares to zero. -/
@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_squared (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) = 0 :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_parts_zero form).1

/-- The actual global antiholomorphic differential squares to zero. -/
@[simp]
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_squared (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form) = 0 :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_parts_zero form).2.2

/-- The two genuine Dolbeault differentials anticommute. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_dPrime_add_dPrime_dDoublePrime (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime form) + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form) = 0 :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.second_derivative_parts_zero form).2.1

/-- The literal `d' d''` is the actual exterior derivative of `d''`, after
only equality transport of the total degree. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_eq_d (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime form).1 =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree
        (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1))
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form).1) := by
  have h := congrArg
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree
      (by omega : p + (q + 1) + 1 = (p + 1) + (q + 1)))
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime form))
  simpa only [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_squared, ZeroMemClass.coe_zero,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_add, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_castDegree,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_zero, add_zero,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_apply] using h

/-- Every actual `d' d''` form is closed. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.d_dPrimeDoublePrime (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime form).1 = 0 := by
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_eq_d, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_castDegree,
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_squared, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_zero]

/-- Every actual `d' d''` form has an explicit primitive for the true incoming
exterior derivative, in the degree used by the de Rham quotient. -/
theorem _root_.OAI.Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_exact (form : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M p q) :
    ∃ primitive : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (((p + 1) + (q + 1)) - 1),
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldIncomingExteriorDerivative E M ((p + 1) + (q + 1)) primitive =
        (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime form).1 := by
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrimeDoublePrime_eq_d]
  exact IncomingDerivativeTransport.exists_incoming_primitive_castDegree_d _ _

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldDolbeaultIdentities.PureManifoldForm
