import OAI.Analysis.HodgeTheory.Decomposition.LefschetzConnection
import OAI.Analysis.HodgeTheory.Decomposition.LefschetzSymbol
import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction
import OAI.Analysis.HodgeTheory.Decomposition.CovariantAdjointPair

/-! # Kahler Commutator -/

namespace OAI.Analysis.HodgeTheory.Decomposition.KahlerCommutator.Constructions

noncomputable section

/-! The full local Kähler commutator, derived from the genuine metric
connection and its parallel inverse Kähler contraction. -/

open scoped ContDiff

attribute [local instance] KoszulSmooth.Constructions.koszulBilinearNormed KoszulSmooth.Constructions.koszulBilinearNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem kahlerCommutator_zero (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E 1) (x : E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v) (hBs : ∀ v w, B x v w = B x w v)
    (hBJ : ∀ v w, B x (Complex.I • v) w = -B x v (Complex.I • w))
    (hΓJ : ∀ v w, Γ x (Complex.I • v) w = Γ x (Complex.I • w) v) :
    LefschetzSymbol.Constructions.metricLefschetzContraction 0 (B x) b
      (CovectorSymbolAction.Constructions.twistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a x) =
      CovariantAdjointPair.Constructions.bilinearCovariantCodifferential b 0 B Γ a x := by
  rw [CovectorSymbolAction.Constructions.twistedExteriorDerivative_covariant b 1 _ Γ a x hΓJ, map_neg, map_sum]
  simp_rw [LefschetzSymbol.Constructions.metricLefschetzContraction_twisted_symbol_zero (B x) hpos hBs hBJ]
  rfl

theorem kahlerCommutator (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : ContDiffOn ℝ ∞ a U)
    (hBs : ∀ v w, B x v w = B x w v)
    (hBJ : ∀ v w, B x (Complex.I • v) w = -B x v (Complex.I • w))
    (hΓ : ∀ u v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (hΓJr : ∀ u v, Γ x u (Complex.I • v) = Complex.I • Γ x u v)
    (hΓJs : ∀ v w, Γ x (Complex.I • v) w = Γ x (Complex.I • w) v) :
    LefschetzSymbol.Constructions.metricLefschetzContraction (n + 1) (B x) b
        (CovectorSymbolAction.Constructions.twistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a x) -
      CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
        (fun y => LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) x =
      CovariantAdjointPair.Constructions.bilinearCovariantCodifferential b (n + 1) B Γ a x := by
  rw [CovectorSymbolAction.Constructions.twistedExteriorDerivative_covariant b (n + 1 + 1) _ Γ a x hΓJs,
    CovectorSymbolAction.Constructions.twistedExteriorDerivative_covariant b n _ Γ _ x hΓJs, map_neg, map_sum, sub_neg_eq_add]
  simp_rw [LefschetzConnection.Constructions.metricLefschetzContraction_parallel b n B Γ a hU hB hpos hx ha _ (hΓ _) (hΓJr _)]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => LefschetzSymbol.Constructions.metricLefschetzContraction_twisted_symbol n (B x) (hpos x hx) hBs hBJ b
      (b.coord i).toContinuousLinearMap (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1 + 1) Γ a x (b i)))
  rw [Finset.sum_sub_distrib] at hs
  have hn := congrArg (fun f : DifferentialForms.Manifold.Basic.FormValue E (n + 1) => -f) hs
  change _ = -(∑ i, SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
    (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1 + 1) Γ a x (b i)))
  convert! hn using 1
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.KahlerCommutator.Constructions
