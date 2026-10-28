import OAI.Analysis.HodgeTheory.Decomposition.CodifferentialSupport
import OAI.Analysis.HodgeTheory.Decomposition.RealMultiplier

/-! # Energy Locality -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EnergyLocality.Constructions

noncomputable section

/-! The actual Hodge energy depends only on a form near the support of
its test form. In particular an outer cutoff equal to one there is harmless. -/

open _root_.MeasureTheory
open scoped _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveCodifferential_congr_on (n : ℕ)
    (a c : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {U : Set V.analyticSpace} (hU : IsOpen U) (hac : ∀ x ∈ U, a x = c x)
    {x : V.analyticSpace} (hx : x ∈ U) :
    AdjointAlgebra.Constructions.projectiveCodifferential V n a x = AdjointAlgebra.Constructions.projectiveCodifferential V n c x := by
  have hzero := CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n (a - c) hU.isClosed_compl
    (fun y hy => by
      change a y - c y = 0
      exact sub_eq_zero.mpr (hac y (by simpa only [Set.mem_compl_iff, not_not] using hy)))
    (x := x) (by simpa only [Set.mem_compl_iff, not_not] using hx)
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

omit [BorelSpace V.analyticSpace] in
theorem projectiveL2Pair_congr_near_test (n : ℕ)
    (a c b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {K U : Set V.analyticSpace} (hKU : K ⊆ U)
    (hac : ∀ x ∈ U, a x = c x) (hb : ∀ x, x ∉ K → b x = 0) :
    Form.Constructions.projectiveL2Pair V n a b = Form.Constructions.projectiveL2Pair V n c b := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  by_cases hx : x ∈ K
  · exact LocalMetric.Constructions.projectiveFormPointPair_congr_at V n a.val b.val c.val b.val x (hac x (hKU hx)) rfl
  · rw [LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n a.val b.val x (hb x hx),
      LocalMetric.Constructions.projectiveFormPointPair_zero_of_right V n c.val b.val x (hb x hx)]

omit [BorelSpace V.analyticSpace] in
theorem projective_d_pair_congr_near_test (n : ℕ)
    (a c b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    {K U : Set V.analyticSpace} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hac : ∀ x ∈ U, a x = c x) (hb : ∀ x, x ∉ K → b x = 0) :
    Form.Constructions.projectiveL2Pair V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) =
      Form.Constructions.projectiveL2Pair V (n + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d c) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) := by
  apply projectiveL2Pair_congr_near_test V (n + 1) _ _ _ hKU
  · intro x hx
    exact DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_congr_on a.val c.val hU hac hx
  · intro x hx
    exact SupportedCoordinates.Constructions.manifold_d_zero_off_closed V n b hK hb hx

theorem projective_delta_pair_congr_near_test (n : ℕ)
    (a c b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    {K U : Set V.analyticSpace} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hac : ∀ x ∈ U, a x = c x) (hb : ∀ x, x ∉ K → b x = 0) :
    Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) (AdjointAlgebra.Constructions.projectiveCodifferential V n b) =
      Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n c) (AdjointAlgebra.Constructions.projectiveCodifferential V n b) := by
  apply projectiveL2Pair_congr_near_test V n _ _ _ hKU
  · exact fun _ hx => projectiveCodifferential_congr_on V n a c hU hac hx
  · exact fun _ hx => CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n b hK hb hx

theorem projective_hodge_energy_real_cutoff (n : ℕ)
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (f : V.analyticSpace → ℝ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    {K U : Set V.analyticSpace} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hfU : ∀ x ∈ U, f x = 1) (hb : ∀ x, x ∉ K → b x = 0) :
    Form.Constructions.projectiveL2Pair V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) +
      Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a) (AdjointAlgebra.Constructions.projectiveCodifferential V n b) =
    Form.Constructions.projectiveL2Pair V (n + 1 + 1)
        (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a)) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b) +
      Form.Constructions.projectiveL2Pair V n (AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a))
        (AdjointAlgebra.Constructions.projectiveCodifferential V n b) := by
  have hac : ∀ x ∈ U, a x = RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a x := by
    intro x hx
    change a x = (f x : ℂ) • a x
    rw [hfU x hx, Complex.ofReal_one, one_smul]
  exact congrArg₂ (fun z w : ℂ => z + w)
    (projective_d_pair_congr_near_test V (n + 1) a _ b hK hU hKU hac hb)
    (projective_delta_pair_congr_near_test V n a _ b hK hU hKU hac hb)

end

end OAI.Analysis.HodgeTheory.Decomposition.EnergyLocality.Constructions
