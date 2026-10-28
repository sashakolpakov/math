import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols

/-! # Kahler Commutator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.KahlerCommutator

noncomputable section

/-! The full local Kähler commutator including the actual complex line-connection term. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.koszulBilinearNormed Analysis.HodgeTheory.Decomposition.KoszulSmooth.Constructions.koszulBilinearNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem lineKahlerCommutator_zero (b : Module.Basis ι ℝ E)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (x : E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v) (hBs : ∀ v w, B x v w = B x w v)
    (hBJ : ∀ v w, B x (Complex.I • v) w = -B x v (Complex.I • w))
    (hΓJ : ∀ v w, Γ x (Complex.I • v) w = Γ x (Complex.I • w) v) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction 0 (B x) b
      (ConnectionSymbols.lineTwistedExteriorDerivative 1 (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) A a x) =
      ConnectionSymbols.lineCovariantCodifferential b 0 B Γ A a x := by
  rw [ConnectionSymbols.lineTwistedExteriorDerivative_covariant b 1 _ Γ A a x hΓJ, map_neg, map_sum]
  simp_rw [Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction_twisted_symbol_zero (B x) hpos hBs hBJ]
  rfl

theorem lineMetricLefschetzContraction_parallel (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : ContDiffOn ℝ ∞ a U) (v : E)
    (hΓ : ∀ u w, B x (Γ x v u) w + B x u (Γ x v w) = fderiv ℝ B x v u w)
    (hΓJ : ∀ u, Γ x v (Complex.I • u) = Complex.I • Γ x v u) :
    ConnectionSymbols.lineCovectorConnectionDerivative n Γ A (fun y => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) x v =
      Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n (B x) b (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1 + 1) Γ A a x v) := by
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, ConnectionSymbols.lineCovectorConnectionDerivative_apply,
    Analysis.HodgeTheory.Decomposition.LefschetzConnection.Constructions.metricLefschetzContraction_parallel b n B Γ a hU hB hpos hx ha v hΓ hΓJ, map_add,
    ConnectionSymbols.metricLefschetzContraction_complex_smul]

theorem lineKahlerCommutator (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : ContDiffOn ℝ ∞ a U)
    (hBs : ∀ v w, B x v w = B x w v)
    (hBJ : ∀ v w, B x (Complex.I • v) w = -B x v (Complex.I • w))
    (hΓ : ∀ u v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (hΓJr : ∀ u v, Γ x u (Complex.I • v) = Complex.I • Γ x u v)
    (hΓJs : ∀ v w, Γ x (Complex.I • v) w = Γ x (Complex.I • w) v) :
    Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction (n + 1) (B x) b
        (ConnectionSymbols.lineTwistedExteriorDerivative (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) A a x) -
      ConnectionSymbols.lineTwistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) A
        (fun y => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) x =
      ConnectionSymbols.lineCovariantCodifferential b (n + 1) B Γ A a x := by
  rw [ConnectionSymbols.lineTwistedExteriorDerivative_covariant b (n + 1 + 1) _ Γ A a x hΓJs,
    ConnectionSymbols.lineTwistedExteriorDerivative_covariant b n _ Γ A _ x hΓJs, map_neg, map_sum, sub_neg_eq_add]
  simp_rw [lineMetricLefschetzContraction_parallel b n B Γ A a hU hB hpos hx ha _ (hΓ _) (hΓJr _)]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions.metricLefschetzContraction_twisted_symbol n (B x) (hpos x hx) hBs hBJ b
      (b.coord i).toContinuousLinearMap (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1 + 1) Γ A a x (b i)))
  rw [Finset.sum_sub_distrib] at hs
  have hn := congrArg (fun f : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1) => -f) hs
  change _ = -(∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction (n + 1) (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap)
    (ConnectionSymbols.lineCovectorConnectionDerivative (n + 1 + 1) Γ A a x (b i)))
  convert! hn using 1
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.KahlerCommutator
