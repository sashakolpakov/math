import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.HessianBilinear
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultAlternation

/-! # Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff

noncomputable section

section

/-! The actual line tensor connection preserves the antiholomorphic projection of its differentiated slot. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.ContinuousAlternatingMap

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem complexAntilinearPart_covectorAction (n : ℕ) (G : E →L[ℝ] E) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) ((Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G).comp N) =
      (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G).comp (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  change (1 / 2 : ℂ) • (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G (N v) + Complex.I • Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G (N (Complex.I • v))) =
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G ((1 / 2 : ℂ) • (N v + Complex.I • N (Complex.I • v)))
  rw [OneCovectorCurvature.covectorInfinitesimalAction_complex_smul, _root_.map_add, OneCovectorCurvature.covectorInfinitesimalAction_complex_smul]

theorem complexAntilinearPart_precomp_J (n : ℕ) (G : E →L[ℝ] E) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hG : ∀ v, G (Complex.I • v) = Complex.I • G v) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N.comp G) =
      (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N).comp G := by
  apply ContinuousLinearMap.ext
  intro v
  change (1 / 2 : ℂ) • (N (G v) + Complex.I • N (G (Complex.I • v))) =
    (1 / 2 : ℂ) • (N (G v) + Complex.I • N (Complex.I • G v))
  rw [hG v]

theorem complexAntilinearPart_tensor_derivative (n : ℕ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v : E) :
    fderiv ℝ (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N y)) x v =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ N x v) := by
  have hd := (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).restrictScalars ℝ).hasFDerivAt.comp x hN.hasFDerivAt).fderiv
  exact congrArg (fun T => T v) hd

theorem lineCovectorTensorDerivative_antilinear (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (N : E → E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {x : E} (hN : DifferentiableAt ℝ N x) (v : E)
    (hG : ∀ w, G x v (Complex.I • w) = Complex.I • G x v w) :
    HessianBilinear.lineCovectorTensorDerivative n G A (fun y => Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N y)) x v =
      Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (HessianBilinear.lineCovectorTensorDerivative n G A N x v) := by
  unfold HessianBilinear.lineCovectorTensorDerivative
  rw [complexAntilinearPart_tensor_derivative n N hN v]
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ N x v) -
      (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N x)).comp (G x v) -
      (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n (G x v)).comp (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N x)) +
      A x v • Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (N x) = _
  rw [← complexAntilinearPart_precomp_J n (G x v) (N x) hG,
    ← complexAntilinearPart_covectorAction n (G x v) (N x),
    _root_.map_add, _root_.map_sub, _root_.map_sub, _root_.map_smul]

end

section

/-! The original line covector derivative obeys the scalar product and gauge laws in a fixed base chart. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionDerivative_scalar (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x) (v : E) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => g y • a y) x v =
      fderiv ℝ g x v • a x + g x • ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v := by
  have hd := congrArg (fun T : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n => T v) (hg.hasFDerivAt.smul ha.hasFDerivAt).fderiv
  simp only [_root_.add_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply] at hd
  change fderiv ℝ (fun y => g y • a y) x v =
    g x • fderiv ℝ a x v + fderiv ℝ g x v • a x at hd
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply, hd,
    ConnectionSymbols.lineCovectorConnectionDerivative_apply, Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply,
    OneCovectorCurvature.covectorInfinitesimalAction_complex_smul]
  module

theorem lineCovectorConnectionDerivative_gauge (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A B : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x)
    (hAB : ∀ v, fderiv ℝ g x v + g x * B x v = g x * A x v) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G B (fun y => g y • a y) x =
      g x • ConnectionSymbols.lineCovectorConnectionDerivative n G A a x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [lineCovectorConnectionDerivative_scalar n G B g a hg ha v]
  change fderiv ℝ g x v • a x + g x • ConnectionSymbols.lineCovectorConnectionDerivative n G B a x v =
    g x • ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v
  rw [ConnectionSymbols.lineCovectorConnectionDerivative_apply, ConnectionSymbols.lineCovectorConnectionDerivative_apply]
  have hv := congrArg (fun c : ℂ => c • a x) (hAB v)
  simp only [add_smul, mul_smul] at hv
  rw [smul_add, smul_add]
  calc
    _ = g x • Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative n G a x v +
        (fderiv ℝ g x v • a x + g x • (B x v • a x)) := by abel
    _ = _ := congrArg (fun t => g x • Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative n G a x v + t) hv

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem lineCovectorAntiDerivative_gauge (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A B : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x)
    (hAB : ∀ v, fderiv ℝ g x v + g x * B x v = g x * A x v) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
      (ConnectionSymbols.lineCovectorConnectionDerivative n G B (fun y => g y • a y) x) =
      g x • Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x) := by
  rw [lineCovectorConnectionDerivative_gauge n G A B g a hg ha hAB, map_smul]

end

section

/-! Exact cutoff commutators for the original covariant Dolbeault differential and metric trace. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.ContinuousAlternatingMap

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

theorem cutoff_symbol_zero_of_scalar_zero {L F : Type} [Zero L] [AddCommMonoid F] [Module ℂ F]
    (S : L → F) (hS : S 0 = 0) {ℓ : L} {g : ℂ} (hℓ : ℓ = 0) (hg : g = 0) (a : F) :
    S ℓ + g • a = 0 := by
  rw [hℓ, hg, hS, zero_smul, add_zero]

section Derivative
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineCovectorConnectionDerivative_scalar_tensor (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x) :
    ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => g y • a y) x =
      ConnectionSymbols.lineConnectionTerm n (fderiv ℝ g x) (a x) + g x • ConnectionSymbols.lineCovectorConnectionDerivative n G A a x := by
  apply ContinuousLinearMap.ext
  intro v
  exact lineCovectorConnectionDerivative_scalar n G A g a hg ha v

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def lineDolbeaultCutoffSymbol (n : ℕ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ConnectionSymbols.lineConnectionTerm n ℓ a))

theorem lineDolbeaultCutoffSymbol_zero (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    lineDolbeaultCutoffSymbol n 0 a = 0 := by
  unfold lineDolbeaultCutoffSymbol ConnectionSymbols.lineConnectionTerm
  rw [ContinuousLinearMap.comp_zero, _root_.map_zero]
  exact _root_.map_zero (alternatizeUncurryFinCLM (n := n) ℝ E ℂ)

theorem lineDolbeaultCutoffSymbol_add_tensor (n : ℕ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (g : ℂ) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ConnectionSymbols.lineConnectionTerm n ℓ a + g • N)) =
      lineDolbeaultCutoffSymbol n ℓ a + g • alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) N) := by
  rw [map_add, map_smul, alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
  rfl

theorem lineCovariantDolbeault_scalar (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x) :
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
      (ConnectionSymbols.lineCovectorConnectionDerivative n G A (fun y => g y • a y) x)) =
        lineDolbeaultCutoffSymbol n (fderiv ℝ g x) (a x) +
          g x • alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
            (ConnectionSymbols.lineCovectorConnectionDerivative n G A a x)) := by
  rw [lineCovectorConnectionDerivative_scalar_tensor n G A g a hg ha,
    map_add, map_smul, alternatizeUncurryFin_add, alternatizeUncurryFin_smul]
  rfl

end Derivative

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

def lineCodifferentialCutoffSymbol (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) : Analysis.DifferentialForms.Manifold.Basic.FormValue E n :=
  -∑ j, ℓ (b j) • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) a

theorem lineCodifferentialCutoffSymbol_zero (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    lineCodifferentialCutoffSymbol b n B 0 a = 0 := by
  simp only [lineCodifferentialCutoffSymbol, _root_.zero_apply, zero_smul, Finset.sum_const_zero, neg_zero]

theorem lineCovariantCodifferential_scalar (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (g : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) {x : E}
    (hg : DifferentiableAt ℝ g x) (ha : DifferentiableAt ℝ a x) :
    ConnectionSymbols.lineCovariantCodifferential b n B G A (fun y => g y • a y) x =
      lineCodifferentialCutoffSymbol b n (B x) (fderiv ℝ g x) (a x) +
        g x • ConnectionSymbols.lineCovariantCodifferential b n B G A a x := by
  unfold ConnectionSymbols.lineCovariantCodifferential lineCodifferentialCutoffSymbol
  simp_rw [lineCovectorConnectionDerivative_scalar (n + 1) G A g a hg ha,
    map_add, ConnectionSymbols.exteriorContraction_complex_smul]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, smul_neg]
  exact neg_add _ _

end

/-! Norm bounds for the actual cutoff commutator symbols. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open _root_.ContinuousAlternatingMap

attribute [local instance] HessianBilinear.tensorConnection_formNormed HessianBilinear.tensorConnection_formSpace
  HessianBilinear.tensorConnection_oneNormed HessianBilinear.tensorConnection_oneSpace

section Linear
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lineConnectionTerm_norm (n : ℕ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    ‖ConnectionSymbols.lineConnectionTerm n ℓ a‖ ≤ ‖ℓ‖ * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [ConnectionSymbols.lineConnectionTerm_apply, norm_smul]
  exact (mul_le_mul_of_nonneg_right (ℓ.le_opNorm v) (norm_nonneg a)).trans_eq (by ring)

theorem exteriorContraction_norm (n : ℕ) (v : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    ‖Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n v a‖ ≤ ‖v‖ * ‖a‖ := by
  have h := a.curryLeft.le_opNorm v
  rw [norm_curryLeft] at h
  exact h.trans_eq (mul_comm _ _)

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem lineDolbeaultCutoffSymbol_norm (n : ℕ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    ‖lineDolbeaultCutoffSymbol n ℓ a‖ ≤
      (‖alternatizeUncurryFinCLM (n := n) ℝ E ℂ‖ * ‖Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)‖ * ‖ℓ‖) * ‖a‖ := by
  have hP := (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)).le_opNorm (ConnectionSymbols.lineConnectionTerm n ℓ a)
  have hL := (alternatizeUncurryFinCLM (n := n) ℝ E ℂ).le_opNorm
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (ConnectionSymbols.lineConnectionTerm n ℓ a))
  have h := hL.trans (mul_le_mul_of_nonneg_left
    (hP.trans (mul_le_mul_of_nonneg_left (lineConnectionTerm_norm n ℓ a) (norm_nonneg _))) (norm_nonneg _))
  exact h.trans_eq (by ring)

end Linear

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem lineCodifferentialCutoffSymbol_norm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (ℓ : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    ‖lineCodifferentialCutoffSymbol b n B ℓ a‖ ≤
      (‖ℓ‖ * ∑ j, ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖) * ‖a‖ := by
  unfold lineCodifferentialCutoffSymbol
  rw [norm_neg]
  calc
    _ ≤ ∑ j, ‖ℓ (b j) • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap) a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, ‖ℓ‖ * ‖b j‖ * ‖Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord j).toContinuousLinearMap‖ * ‖a‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact (mul_le_mul (ℓ.le_opNorm _) (exteriorContraction_norm n _ a) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff
