import OAI.RepresentationTheory.Theta.AdelicSupport
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Convergence -/

namespace OAI.RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction

noncomputable section

/-! Absolute convergence of the adelic rational theta functional and of
its Gaussian specialization. No representation or Poisson hypothesis is needed. -/

open scoped Classical
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι]

theorem weighted_rational_summable_on
    (L : Submodule ℤ (ι → ℝ)) (f : (ι → ℝ) → ℂ)
    (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (hL : ∀ x : ι → ℚ, φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → PoissonAutomorphyNormalizationData.Construction.rationalReal x ∈ L)
    (hf : Summable (fun y : L => ‖f y.val‖)) :
    Summable (fun x : ι → ℚ => ‖φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) * f (PoissonAutomorphyNormalizationData.Construction.rationalReal x)‖) := by
  let S : Set (ι → ℚ) := {x | φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0}
  let e : S → L := fun x => ⟨PoissonAutomorphyNormalizationData.Construction.rationalReal x.val, hL x.val x.property⟩
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    apply PoissonAutomorphyNormalizationData.Construction.rationalReal_injective
    exact congrArg Subtype.val h
  apply (summable_subtype_and_compl (s := S)).mp
  constructor
  · obtain ⟨C, hC⟩ := PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_bounded φ
    apply ((hf.comp_injective he).mul_left C).of_nonneg_of_le
      (fun _ => norm_nonneg _)
    intro x
    change ‖φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x.val) * f (PoissonAutomorphyNormalizationData.Construction.rationalReal x.val)‖ ≤
      C * ‖f (PoissonAutomorphyNormalizationData.Construction.rationalReal x.val)‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · have hz : (fun x : ↥(Sᶜ) =>
        ‖φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x.val) * f (PoissonAutomorphyNormalizationData.Construction.rationalReal x.val)‖) = 0 := by
      funext x
      have hzero : φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x.val) = 0 := by
        simpa only [S, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using x.property
      simp only [hzero, zero_mul, norm_zero, Pi.zero_apply]
    rw [hz]
    exact summable_zero

theorem tensor_rational_norm_summable (f : PoissonAutomorphyNormalizationData.realSchwartz ι) (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    Summable (fun x : ι → ℚ => ‖PoissonAutomorphyNormalizationData.pureTensor f φ (PoissonAutomorphyNormalizationData.diagonal x)‖) := by
  obtain ⟨n, hn, hden⟩ := AdelicSupport.PoissonAutomorphyConstruction.finiteSchwartz_denominator φ
  let : DiscreteTopology (PoissonAutomorphyNormalizationData.Construction.scaledLattice (ι := ι) n) := PoissonAutomorphyNormalizationData.Construction.scaledLattice_discrete n hn
  obtain ⟨F, hF⟩ := (PoissonAutomorphyNormalizationData.Construction.realSchwartz_mem_iff f.val).mp f.property
  have hf : Summable (fun y : PoissonAutomorphyNormalizationData.Construction.scaledLattice (ι := ι) n => ‖f.val y.val‖) := by
    rw [hF]
    exact PoissonAutomorphyNormalizationData.Construction.schwartz_lattice_summable (PoissonAutomorphyNormalizationData.Construction.scaledLattice n) F
  have h := weighted_rational_summable_on (PoissonAutomorphyNormalizationData.Construction.scaledLattice n) f.val φ
    (fun x hx => PoissonAutomorphyNormalizationData.Construction.rationalReal_mem_scaledLattice n x (hden x hx)) hf
  change Summable (fun x : ι → ℚ =>
    ‖f.val (PoissonAutomorphyNormalizationData.Construction.rationalReal x) * φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x)‖)
  exact h.congr (fun _ => by rw [mul_comm])

theorem adelic_rational_norm_summable (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    Summable (fun x : ι → ℚ => ‖f.val (PoissonAutomorphyNormalizationData.diagonal x)‖) := by
  obtain ⟨F, hF⟩ := f
  change Summable (fun x : ι → ℚ => ‖F (PoissonAutomorphyNormalizationData.diagonal x)‖)
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨g, φ, rfl⟩ := hF
    exact tensor_rational_norm_summable g φ
  | zero => simp
  | add F G _ _ hF hG =>
    apply (hF.add hG).of_nonneg_of_le (fun _ => norm_nonneg _)
    intro x
    exact norm_add_le _ _
  | smul c F _ hF =>
    simpa only [Pi.smul_apply, norm_smul] using hF.mul_left ‖c‖

theorem adelic_rational_summable (f : PoissonAutomorphyNormalizationData.adelicSchwartz ι) :
    Summable (fun x : ι → ℚ => f.val (PoissonAutomorphyNormalizationData.diagonal x)) :=
  (adelic_rational_norm_summable f).of_norm

def thetaLinearFunctional : PoissonAutomorphyNormalizationData.adelicSchwartz ι →ₗ[ℂ] ℂ where
  toFun := PoissonAutomorphyNormalizationData.thetaFunctional
  map_add' f g := (adelic_rational_summable f).tsum_add (adelic_rational_summable g)
  map_smul' c f := by
    change (∑' x : ι → ℚ, c * f.val (PoissonAutomorphyNormalizationData.diagonal x)) = c * ∑' x, f.val (PoissonAutomorphyNormalizationData.diagonal x)
    exact tsum_mul_left

theorem thetaTerm_eq_weightedPhase (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) (x : ι → ℚ) :
    PoissonAutomorphyNormalizationData.thetaTerm φ Z z x = φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) *
      Z.phase.thetaTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (PoissonAutomorphyNormalizationData.Construction.rationalReal x) z := by
  simp only [PoissonAutomorphyNormalizationData.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase.thetaTerm, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
    AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, PoissonAutomorphyNormalizationData.Construction.rationalReal, Complex.ofReal_ratCast]
  rfl

theorem gaussian_rational_norm_summable (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    Summable (fun x : ι → ℚ => ‖PoissonAutomorphyNormalizationData.thetaTerm φ Z z x‖) := by
  obtain ⟨n, hn, hden⟩ := AdelicSupport.PoissonAutomorphyConstruction.finiteSchwartz_denominator φ
  let : DiscreteTopology (PoissonAutomorphyNormalizationData.Construction.scaledLattice (ι := ι) n) := PoissonAutomorphyNormalizationData.Construction.scaledLattice_discrete n hn
  have h := weighted_rational_summable_on (PoissonAutomorphyNormalizationData.Construction.scaledLattice n)
    (fun y => Z.phase.thetaTerm (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) y z) φ
    (fun x hx => PoissonAutomorphyNormalizationData.Construction.rationalReal_mem_scaledLattice n x (hden x hx))
    (Z.phase.thetaTerm_norm_summable (AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing ι) (PoissonAutomorphyNormalizationData.Construction.scaledLattice n) z)
  simpa only [thetaTerm_eq_weightedPhase] using h

end

end OAI.RepresentationTheory.Theta.Convergence.PoissonAutomorphyConstruction
