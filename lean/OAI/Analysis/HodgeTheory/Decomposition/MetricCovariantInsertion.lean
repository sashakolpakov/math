import OAI.Analysis.HodgeTheory.Decomposition.CovariantInsertion
import OAI.Analysis.HodgeTheory.Decomposition.KoszulSmooth

/-! # Metric Covariant Insertion -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion.Constructions

noncomputable section

/-! Covariant differentiation of inverse-metric insertion, proved using
the actual inverse-metric derivative. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exteriorContraction_neg_vector (n : ℕ) (w : E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    SymbolDifferential.Constructions.exteriorContraction n (-w) a = -SymbolDifferential.Constructions.exteriorContraction n w a := a.curryLeft.map_neg w

theorem metricCovariantInsertion (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : DifferentiableAt ℝ a x) (u : E)
    (hΓ : ∀ v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (ξ : E →L[ℝ] ℝ) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp (B y) ξ) (a y)) x u =
      -SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (Γ x u))) (a x) +
        SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1) Γ a x u) := by
  have hw := (((KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply
    (contDiffOn_const (c := ξ))).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [CovariantInsertion.Constructions.covectorConnectionDerivative_contraction n Γ a _ ha hw,
    KoszulSmooth.Constructions.bilinearMetricSharp_derivative B hU hB hpos hx u (Γ x u) hΓ ξ]
  have hv : -Γ x u (KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) -
      KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (Γ x u)) + Γ x u (KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) =
      -KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (Γ x u)) := by abel
  rw [hv, exteriorContraction_neg_vector]

theorem metricCovariantDoubleInsertion (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : ContDiffOn ℝ ∞ a U) (u v : E)
    (hΓ : ∀ v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (ξ : E →L[ℝ] ℝ) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ
      (fun y => SymbolDifferential.Constructions.exteriorContraction n v (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B y) ξ) (a y))) x u =
      SymbolDifferential.Constructions.exteriorContraction n (Γ x u v) (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ) (a x)) -
        SymbolDifferential.Constructions.exteriorContraction n v (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) (ξ.comp (Γ x u))) (a x)) +
      SymbolDifferential.Constructions.exteriorContraction n v (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) ξ)
        (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1 + 1) Γ a x u)) := by
  have hw := (KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos).clm_apply (contDiffOn_const (c := ξ))
  have hi := ((CovariantInsertion.Constructions.exteriorContraction_smoothOn (n + 1) a _ ha hw).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [CovariantInsertion.Constructions.covectorConnectionDerivative_const_contraction n Γ _ v hi,
    metricCovariantInsertion (n + 1) B Γ a hU hB hpos hx
      ((ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)) u hΓ ξ,
    map_add, map_neg]
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion.Constructions
