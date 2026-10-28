import OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents

/-! # Schwartz Coordinates -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SchwartzCoordinates.Constructions

noncomputable section

section

/-! Scalar orthonormal coordinates of vector-valued Schwartz functions,
including their actual directional derivatives and Sobolev bounds. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

theorem schwartz_postcomp_toLp (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    (SchwartzMap.postcompCLM L f).toLp 2 volume = L.compLpL 2 volume (f.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM L f).coeFn_toLp 2 volume,
    L.coeFn_compLpL (f.toLp 2 volume), f.coeFn_toLp 2 volume] with x hx hy hz
  rw [hx, hy, hz]
  rfl

theorem schwartz_postcomp_lp_bound (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    ‖(SchwartzMap.postcompCLM L f).toLp 2 volume‖ ≤ ‖L‖ * ‖f.toLp 2 volume‖ := by
  rw [schwartz_postcomp_toLp]
  exact L.norm_compLp_le _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartz_postcomp_directional (L : F →L[ℂ] G) (f : 𝓢(E, F)) (m : E) :
    ∂_{m} (SchwartzMap.postcompCLM L f) = SchwartzMap.postcompCLM L (∂_{m} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.postcompCLM_apply]
  exact congrArg (fun A : E →L[ℝ] G => A m)
    (((L.restrictScalars ℝ).hasFDerivAt.comp x f.differentiableAt.hasFDerivAt).fderiv)

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def schwartzOrthonormalCoordinate (b : OrthonormalBasis κ ℂ F) (j : κ) :
    𝓢(E, F) →L[ℂ] 𝓢(E, ℂ) := SchwartzMap.postcompCLM (innerSL ℂ (b j))

theorem schwartzOrthonormalCoordinate_lp_bound (b : OrthonormalBasis κ ℂ F) (j : κ) (f : 𝓢(E, F)) :
    ‖(schwartzOrthonormalCoordinate b j f).toLp 2 volume‖ ≤ ‖f.toLp 2 volume‖ := by
  have h := schwartz_postcomp_lp_bound (innerSL ℂ (b j)) f
  simpa only [schwartzOrthonormalCoordinate, innerSL_apply_norm, b.norm_eq_one, one_mul] using h

theorem schwartzOrthonormalCoordinate_sobolev_bound
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℂ F) (j : κ) (f : 𝓢(E, F)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevNorm 1 (schwartzOrthonormalCoordinate c j f) ≤ ‖f.toLp 2 volume‖ +
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * ∑ i, ‖(∂_{b i} f).toLp 2 volume‖ := by
  have h := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothEstimate.CM.Construction.schwartzSobolevCoordinate_one_bound b (schwartzOrthonormalCoordinate c j f)
  apply h.trans
  apply add_le_add (schwartzOrthonormalCoordinate_lp_bound c j f)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  change ‖(∂_{b i} (SchwartzMap.postcompCLM (innerSL ℂ (c j)) f)).toLp 2 volume‖ ≤ _
  rw [schwartz_postcomp_directional]
  exact schwartzOrthonormalCoordinate_lp_bound c j (∂_{b i} f)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzOrthonormalCoordinate_support
    (b : OrthonormalBasis κ ℂ F) (j : κ) (f : 𝓢(E, F)) :
    Function.support (schwartzOrthonormalCoordinate b j f) ⊆ Function.support f := by
  intro x hx hzero
  apply hx
  change inner ℂ (b j) (f x) = 0
  rw [hzero, inner_zero_right]

end

/-! Rellich compactness for the actual finite-dimensional coefficient spaces
of differential forms, obtained from scalar Rellich and finite orthonormal synthesis. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap

variable {E F κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype κ]

def synthesizeLpCoordinates (b : OrthonormalBasis κ ℂ F) :
    (κ → Lp ℂ 2 (volume : Measure E)) →L[ℂ] Lp F 2 (volume : Measure E) :=
  (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lpOrthonormalSynthesis b).comp
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => Lp ℂ 2 (volume : Measure E))).symm.toContinuousLinearMap

theorem schwartz_synthesizeLpCoordinates (b : OrthonormalBasis κ ℂ F) (f : 𝓢(E, F)) :
    synthesizeLpCoordinates b (fun j => (schwartzOrthonormalCoordinate b j f).toLp 2 volume) =
      f.toLp 2 volume := by
  let u : PiLp 2 (fun _ : κ => Lp ℂ 2 (volume : Measure E)) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => Lp ℂ 2 (volume : Measure E))).symm
      (fun j => (schwartzOrthonormalCoordinate b j f).toLp 2 volume)
  have hcoord : ∀ᵐ x ∂(volume : Measure E), ∀ j : κ, u j x = inner ℂ (b j) (f x) :=
    ae_all_iff.mpr (fun j => (schwartzOrthonormalCoordinate b j f).coeFn_toLp 2 volume)
  apply Lp.ext
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lpOrthonormalSynthesis_coe b u, hcoord, f.coeFn_toLp 2 volume] with x hx hy hf
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lpOrthonormalSynthesis b u x = _
  rw [hx, hf]
  simp only [hy]
  exact b.sum_repr' (f x)

theorem schwartz_vector_rellich_compact
    (b : OrthonormalBasis κ ℂ F) {K : Set E} (hK : IsCompact K) (C : ℝ) :
    IsCompact (closure ((fun f : 𝓢(E, F) => f.toLp 2 volume) ''
      {f | Function.support f ⊆ K ∧
        ∀ j, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevNorm 1 (schwartzOrthonormalCoordinate b j f) ≤ C})) := by
  let T := closure ((fun f : 𝓢(E, ℂ) => f.toLp 2 volume) ''
    {f | Function.support f ⊆ K ∧ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevNorm 1 f ≤ C})
  have hT : IsCompact T := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartz_rellich_compact hK C
  have hP : IsCompact (Set.pi Set.univ (fun _ : κ => T)) := by
    have heq : Set.pi Set.univ (fun _ : κ => T) = {x | ∀ j, x j ∈ T} := by
      ext x
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq]
    rw [heq]
    exact isCompact_pi_infinite (fun _ : κ => hT)
  have hS := hP.image (synthesizeLpCoordinates (E := E) b).continuous
  apply hS.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hS.isClosed
  rintro _ ⟨f, ⟨hf, hnorm⟩, rfl⟩
  refine ⟨fun j => (schwartzOrthonormalCoordinate b j f).toLp 2 volume, ?_,
    schwartz_synthesizeLpCoordinates b f⟩
  intro j _
  apply subset_closure
  exact ⟨schwartzOrthonormalCoordinate b j f,
    ⟨(schwartzOrthonormalCoordinate_support b j f).trans hf, hnorm j⟩, rfl⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.SchwartzCoordinates.Constructions
