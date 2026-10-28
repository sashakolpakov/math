import OAI.RepresentationTheory.Theta.Kernel.AdelicSupport
import OAI.RepresentationTheory.Theta.Definitions
import OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums

/-! # Analysis -/

namespace OAI.RepresentationTheory.Theta.Kernel.Analysis

noncomputable section

open scoped BigOperators _root_.Topology BoundedContinuousFunction _root_.Matrix.Norms.Elementwise
open Filter OAI.AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM

abbrev ThetaParameters (ι : Type*) := (ι → ι → ℂ) × (ι → ℂ)

variable {ι : Type*} [Fintype ι]

def latticeSummand (L : Submodule ℤ (ι → ℝ)) (φ : L →ᵇ ℂ)
    (x : L) (p : ThetaParameters ι) : ℂ :=
  φ x * Complex.exp
    ((Real.pi : ℂ) * Complex.I *
        AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm p.1 (x : ι → ℝ) (x : ι → ℝ) +
      (2 * (Real.pi : ℂ) * Complex.I) *
        (∑ i, (((x : ι → ℝ) i : ℝ) : ℂ) * p.2 i))

/-- The full GaussianConvergence proposition, with only its parameter type unfolded. -/
def GaussianConvergenceInput (ι : Type*) [Fintype ι] : Prop :=
  ∀ (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (φ : L →ᵇ ℂ) (K : Set (ThetaParameters ι)),
    IsCompact K →
    (∀ p ∈ K, p.1 ∈ Definitions.siegelDomain) →
    ∀ m : ℕ,
    let Θ : ThetaParameters ι → ℂ :=
      fun p => Definitions.theta L φ p.1 p.2
    (∃ C c b : ℝ,
      let M : L → ℝ := fun x =>
        C * (1 + ‖(x : ι → ℝ)‖) ^ (2 * m) *
          Real.exp (-c * ‖(x : ι → ℝ)‖ ^ 2 + b * ‖(x : ι → ℝ)‖)
      0 < C ∧ 0 < c ∧ 0 ≤ b ∧ Summable M ∧
        ∀ k ≤ m, ∀ x : L, ∀ p ∈ K,
          ‖iteratedFDeriv ℂ k (latticeSummand L φ x) p‖ ≤ M x) ∧
    (∀ p ∈ K, ContDiffAt ℂ ⊤ Θ p) ∧
    (∀ k ≤ m, ∀ p ∈ K,
      HasSum (fun x : L => iteratedFDeriv ℂ k (latticeSummand L φ x) p)
        (iteratedFDeriv ℂ k Θ p)) ∧
    (∀ k ≤ m, ∀ a : L,
      TendstoUniformlyOn
        (fun n p => AlgebraicGeometry.ComplexMultiplication.SparseLatticeSums.CM.sparseLatticeSum L
          (fun x => iteratedFDeriv ℂ k (latticeSummand L φ x) p) a n)
        (fun p => iteratedFDeriv ℂ k (latticeSummand L φ a) p) atTop K)

lemma lattice_analysis (h_GaussianConvergence : GaussianConvergenceInput ι)
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (φ : L →ᵇ ℂ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Summable (fun x : L => latticeSummand L φ x (Z.matrix, z)) ∧
    ContDiffAt ℂ ⊤ (fun w => Definitions.theta L φ Z.matrix w) z := by
  classical
  have hpos : ∀ p ∈ ({(Z.matrix, z)} : Set (ThetaParameters ι)),
      p.1 ∈ Definitions.siegelDomain := by
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨Z.symmetric, Z.imaginary_posDef⟩
  obtain ⟨hbound, hsmooth, _⟩ :=
    h_GaussianConvergence L φ {(Z.matrix, z)} isCompact_singleton hpos 0
  obtain ⟨C, c, b, _, _, _, hsum, hb⟩ := hbound
  constructor
  · apply hsum.of_norm_bounded
    intro x
    simpa using hb 0 le_rfl x (Z.matrix, z) (Set.mem_singleton _)
  · exact (hsmooth (Z.matrix, z) (Set.mem_singleton _)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)

lemma adelic_analysis (h_GaussianConvergence : GaussianConvergenceInput ι)
    (φ : Definitions.DerivativeFactorization.Input ι) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) :
    (∀ z, Summable (fun r : ι → ℚ => φ.1 (Definitions.DerivativeFactorization.diagonal r) * Definitions.DerivativeFactorization.kernel Z.matrix r z)) ∧
    ContDiff ℂ ⊤ (Definitions.DerivativeFactorization.completed φ Z) := by
  classical
  obtain ⟨L, hL, q, hqi, hq, hsupport⟩ := AdelicSupport.input_lattice_presentation φ
  let : DiscreteTopology L := hL
  obtain ⟨C, hC⟩ := AdelicSupport.input_bounded φ
  let ψ : L →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => φ.1 (Definitions.DerivativeFactorization.diagonal (q x))) C (fun x => hC _)
  have hterm : ∀ (B : Matrix ι ι ℂ) z x,
      φ.1 (Definitions.DerivativeFactorization.diagonal (q x)) * Definitions.DerivativeFactorization.kernel B (q x) z = latticeSummand L ψ x (B, z) := by
    intro B z x
    simp only [Definitions.DerivativeFactorization.kernel, latticeSummand, hq, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
    rfl
  have hzero : ∀ z r, r ∉ Set.range q →
      φ.1 (Definitions.DerivativeFactorization.diagonal r) * Definitions.DerivativeFactorization.kernel Z.matrix r z = 0 := by
    intro z r hr
    have hp : φ.1 (Definitions.DerivativeFactorization.diagonal r) = 0 := by
      by_contra h
      exact hr (hsupport r h)
    rw [hp, zero_mul]
  have heq : Definitions.DerivativeFactorization.theta φ Z.matrix =
      fun z => Definitions.theta L ψ Z.matrix z := by
    funext z
    have he := hqi.tsum_eq (f := fun r => φ.1 (Definitions.DerivativeFactorization.diagonal r) * Definitions.DerivativeFactorization.kernel Z.matrix r z)
      (fun r hr => by
        by_contra h
        exact hr (hzero z r h))
    simpa only [Definitions.DerivativeFactorization.theta, Definitions.theta, hterm, latticeSummand] using he.symm
  constructor
  · intro z
    apply (hqi.summable_iff (hzero z)).mp
    simpa only [Function.comp_def, hterm] using (lattice_analysis h_GaussianConvergence L ψ Z z).1
  · have hs : ContDiff ℂ ⊤ (Definitions.DerivativeFactorization.theta φ Z.matrix) := by
      rw [heq, contDiff_iff_contDiffAt]
      exact fun z => (lattice_analysis h_GaussianConvergence L ψ Z z).2
    have hc : ContDiff ℂ ⊤ (AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm) := by
      exact Complex.contDiff_exp.comp (Z.completionForm.contDiff.clm_apply contDiff_id)
    exact hc.mul hs

end

end OAI.RepresentationTheory.Theta.Kernel.Analysis
