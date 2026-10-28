import OAI.Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion
import OAI.Analysis.HodgeTheory.Decomposition.BivectorBasisTransport
import OAI.Analysis.HodgeTheory.Decomposition.ConnectionLinearCalculus

/-! # Lefschetz Connection -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LefschetzConnection.Constructions

noncomputable section

/-! Inverse Kähler contraction is parallel for the actual metric-compatible,
complex-structure-preserving connection. -/

open scoped ContDiff

attribute [local instance] KoszulSmooth.Constructions.koszulBilinearNormed KoszulSmooth.Constructions.koszulBilinearNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

omit [IsScalarTower ℝ ℂ E] in
theorem metricLefschetzContraction_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E}
    (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (fun y => LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) U := by
  have hsharp := KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hw (i : ι) := ContDiffOn.clm_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (G := E)
    hsharp (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  have hi (i : ι) := CovariantInsertion.Constructions.exteriorContraction_smoothOn n
    (fun y => SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap) (a y))
    (fun _ => Complex.I • b i)
    (CovariantInsertion.Constructions.exteriorContraction_smoothOn (n + 1) a _ ha
      (hw i)) contDiffOn_const
  have hs := (ContDiffOn.sum (s := Finset.univ) (fun i _ => hi i)).const_smul (1 / 2 : ℝ)
  simpa only [LefschetzSymbol.Constructions.metricLefschetzContraction, smul_apply, BivectorContraction.Constructions.bivectorContraction_apply] using hs

theorem metricLefschetzContraction_parallel (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hpos : ∀ y ∈ U, ∀ v : E, v ≠ 0 → 0 < B y v v)
    {x : E} (hx : x ∈ U) (ha : ContDiffOn ℝ ∞ a U) (u : E)
    (hΓ : ∀ v w, B x (Γ x u v) w + B x v (Γ x u w) = fderiv ℝ B x u v w)
    (hΓJ : ∀ v, Γ x u (Complex.I • v) = Complex.I • Γ x u v) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) x u =
      LefschetzSymbol.Constructions.metricLefschetzContraction n (B x) b (CovectorConnection.Constructions.covectorConnectionDerivative (n + 1 + 1) Γ a x u) := by
  let ψ (i : ι) (y : E) := SymbolDifferential.Constructions.exteriorContraction n (Complex.I • b i)
    (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B y) (b.coord i).toContinuousLinearMap) (a y))
  have hsharp := KoszulSmooth.Constructions.bilinearMetricSharp_smoothOn B hU hB hpos
  have hw (i : ι) := ContDiffOn.clm_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ) (G := E)
    hsharp (contDiffOn_const (c := (b.coord i).toContinuousLinearMap))
  have hψ (i : ι) : ContDiffOn ℝ ∞ (ψ i) U :=
    CovariantInsertion.Constructions.exteriorContraction_smoothOn n _ (fun _ => Complex.I • b i)
      (CovariantInsertion.Constructions.exteriorContraction_smoothOn (n + 1) a _ ha
        (hw i)) contDiffOn_const
  have hψd (i : ι) := ((hψ i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hsum := ((ContDiffOn.sum (s := Finset.univ) (fun i _ => hψ i)).contDiffAt
    (hU.mem_nhds hx)).differentiableAt (by simp)
  have hform : (fun y => LefschetzSymbol.Constructions.metricLefschetzContraction n (B y) b (a y)) =
      (fun y => (1 / 2 : ℝ) • ∑ i, ψ i y) := by
    funext y
    simp only [LefschetzSymbol.Constructions.metricLefschetzContraction, smul_apply, BivectorContraction.Constructions.bivectorContraction_apply]
    rfl
  rw [hform, ConnectionLinearCalculus.Constructions.covectorConnectionDerivative_real_smul n Γ _ hsum,
    ConnectionLinearCalculus.Constructions.covectorConnectionDerivative_sum n Γ ψ hψd]
  have hd (i : ι) := MetricCovariantInsertion.Constructions.metricCovariantDoubleInsertion n B Γ a hU hB hpos hx ha u
    (Complex.I • b i) hΓ (b.coord i).toContinuousLinearMap
  change ∀ i, CovectorConnection.Constructions.covectorConnectionDerivative n Γ (ψ i) x u = _ at hd
  simp_rw [hd, hΓJ]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcancel := BivectorBasisTransport.Constructions.bivector_basis_transport b n (KoszulConnection.Constructions.bilinearMetricSharp (B x))
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (Γ x u) (a x)
  change (∑ i, SymbolDifferential.Constructions.exteriorContraction n (Complex.I • b i)
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) ((b.coord i).toContinuousLinearMap.comp (Γ x u))) (a x))) =
    ∑ i, SymbolDifferential.Constructions.exteriorContraction n (Complex.I • Γ x u (b i))
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x)) at hcancel
  rw [hcancel, sub_self, zero_add]
  simp only [LefschetzSymbol.Constructions.metricLefschetzContraction, smul_apply, BivectorContraction.Constructions.bivectorContraction_apply]

end

end OAI.Analysis.HodgeTheory.Decomposition.LefschetzConnection.Constructions
