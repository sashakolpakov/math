import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalPeriodGraphs
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Moving Total Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod.CM

noncomputable section

/-! ThetaCycle: every approximating splitting has a positive total period in the
original rational coordinates, with its actual ambient graph identified. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

theorem symplectic_graph_substitution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (x : ι → ℂ) :
    Matrix.fromBlocks g.complexify.A g.complexify.B g.complexify.C g.complexify.D *ᵥ
      Sum.elim (Z.matrix *ᵥ x) x =
    Sum.elim ((g.transformSiegel Z).matrix *ᵥ (g.complexify.denominator Z.matrix *ᵥ x))
      (g.complexify.denominator Z.matrix *ᵥ x) := by
  have hf := g.complexify.fractional_mul_denominator Z.matrix (g.denominator_det_isUnit Z)
  change _ = Sum.elim (g.complexify.fractional Z.matrix *ᵥ _) _
  rw [Matrix.mulVec_mulVec, hf]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.numerator, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.denominator,
    Matrix.add_mulVec, Matrix.mulVec_mulVec]

theorem rational_symplectic_blocks_complex {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) :
    Matrix.fromBlocks (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D = γ.val.map (algebraMap ℚ ℂ) := by
  change Matrix.fromBlocks
    (((γ.val.map (algebraMap ℚ ℝ)).toBlocks₁₁).map (algebraMap ℝ ℂ))
    (((γ.val.map (algebraMap ℚ ℝ)).toBlocks₁₂).map (algebraMap ℝ ℂ))
    (((γ.val.map (algebraMap ℚ ℝ)).toBlocks₂₁).map (algebraMap ℝ ℂ))
    (((γ.val.map (algebraMap ℚ ℝ)).toBlocks₂₂).map (algebraMap ℝ ℂ)) = _
  rw [← Matrix.fromBlocks_map, Matrix.fromBlocks_toBlocks, Matrix.map_map]
  ext i j
  simp

theorem rational_symplectic_graph_substitution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (x : ι → ℂ) :
    γ.val.map (algebraMap ℚ ℂ) *ᵥ Sum.elim (Z.matrix *ᵥ x) x =
      Sum.elim (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix *ᵥ
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix *ᵥ x))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix *ᵥ x) := by
  rw [← rational_symplectic_blocks_complex]
  exact symplectic_graph_substitution (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z x

theorem symplectic_period_holomorphic
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [Fintype ι] [DecidableEq ι] {s : Set V}
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (hZ : DifferentiableOn ℂ (fun z => (Z z).matrix) s) :
    DifferentiableOn ℂ (fun z => (g.transformSiegel (Z z)).matrix) s := by
  have hm (M N : Matrix ι ι ℂ) :
      DifferentiableOn ℂ (fun z => M * (Z z).matrix + N) s :=
    (MatrixCalculus.CM.matrix_product_holomorphic (fun _ => M) (fun z => (Z z).matrix)
      (differentiableOn_const _) hZ).add (differentiableOn_const _)
  change DifferentiableOn ℂ (fun z =>
    (g.complexify.A * (Z z).matrix + g.complexify.B) *
      (g.complexify.C * (Z z).matrix + g.complexify.D)⁻¹) s
  apply MatrixCalculus.CM.matrix_product_holomorphic _ _ (hm _ _)
  apply MatrixCalculus.CM.matrix_inverse_holomorphic _ (hm _ _)
  intro z _
  exact (isUnit_iff_ne_zero.mp (g.denominator_det_isUnit (Z z)))

theorem block_period_holomorphic
    {V ι κ : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [Fintype ι] [Fintype κ] {s : Set V}
    (Z₀ : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Z₁ : V → ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix κ)
    (h₀ : DifferentiableOn ℂ (fun z => (Z₀ z).matrix) s)
    (h₁ : DifferentiableOn ℂ (fun z => (Z₁ z).matrix) s) :
    DifferentiableOn ℂ (fun z => (BlockPeriod.CM.blockPeriod (Z₀ z) (Z₁ z)).matrix) s := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  cases i <;> cases j <;> simp only [BlockPeriod.CM.blockPeriod, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · fun_prop
  · exact differentiableOn_const _
  · exact differentiableOn_const _
  · fun_prop

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)

/-- The approximating total period is expressed in the original coordinate
system of the fixed total finite Schwartz input. Positivity is constructed
by the native symplectic Siegel action. -/
def approximationTotalPeriod (z : HeckeCycles.GeometricSource.CM.BallChart) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (PeriodTotal.CM.TotalPositions K D.places) :=
  (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).transformSiegel
    (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z))

theorem approximation_total_period_holomorphic :
    DifferentiableOn ℂ (fun z => (approximationTotalPeriod K D A z).matrix) D.ball.domain :=
  symplectic_period_holomorphic _ _
    (block_period_holomorphic _ _ (A.periods 0).holomorphic (A.periods 1).holomorphic)

theorem approximation_total_graph (z : HeckeCycles.GeometricSource.CM.BallChart) (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)
    let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator Z.matrix
    TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (D.initialPeriods i).coordinates)
      (approximationTotalPeriod K D A z) (J *ᵥ x) =
    ComplexTransition.CM.complexTensorBasisChange K A.basis
      (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun i => (A.periods i).coordinates) Z x) := by
  dsimp only
  apply (ComplexTransition.CM.totalComplexCoordinates K (fun i => (D.initialPeriods i).coordinates)).injective
  rw [TotalPeriodGraphs.CM.total_graph_coordinates, ← TotalPeriodGraphs.CM.total_transition_graph]
  exact (rational_symplectic_graph_substitution (PeriodTotal.CM.approximationSymplecticMatrix K D A)
    (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)) x).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod.CM
