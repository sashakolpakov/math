import OAI.Analysis.HodgeTheory.Decomposition.EnergyDomain

/-! # Weak Resolvent -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakResolvent.Constructions

noncomputable section

/-! Unconditional weak solvability of the regularized Hodge equation on the
actual Hilbert energy domain. No compactness or regularity assumption is added. -/

open scoped _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] (n : ℕ)

/-- The weak solution of `(1 + Δ)u = f`, supplied by Riesz representation in the actual graph norm. -/
def projectiveWeakResolvent (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) : EnergyDomain.Constructions.ProjectiveEnergyDomain V n :=
  (InnerProductSpace.toDual ℂ (EnergyDomain.Constructions.ProjectiveEnergyDomain V n)).symm
    ((innerSL ℂ f).comp (EnergyDomain.Constructions.projectiveEnergyInclusion V n))

theorem projectiveWeakResolvent_pair
    (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) (v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) :
    inner ℂ (projectiveWeakResolvent V n f) v =
      inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) :=
  InnerProductSpace.toDual_symm_apply

/-- Every L² forcing term has a unique weak solution of the regularized equation. -/
theorem projective_regularized_weak_existsUnique (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    ∃! u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n, ∀ v : EnergyDomain.Constructions.ProjectiveEnergyDomain V n,
      inner ℂ (EnergyDomain.Constructions.projectiveEnergyInclusion V n u) (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) +
        inner ℂ (EnergyDomain.Constructions.projectiveEnergyDerivative V n u) (EnergyDomain.Constructions.projectiveEnergyDerivative V n v) =
          inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n v) := by
  refine ⟨projectiveWeakResolvent V n f, ?_, ?_⟩
  · intro v
    rw [← EnergyDomain.Constructions.projectiveEnergyDomain_inner, projectiveWeakResolvent_pair]
  · intro u hu
    apply ext_inner_right ℂ
    intro v
    rw [projectiveWeakResolvent_pair, EnergyDomain.Constructions.projectiveEnergyDomain_inner]
    exact hu v

theorem projectiveEnergyInclusion_norm_le_one : ‖EnergyDomain.Constructions.projectiveEnergyInclusion V n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖u.val.fst‖ ≤ 1 * ‖u‖
  rw [one_mul]
  exact WithLp.norm_fst_le (Form.Constructions.ProjectiveL2Forms V (n + 1)) u.val

/-- The weak resolvent is bounded directly by the forcing norm. -/
theorem projectiveWeakResolvent_norm_le (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    ‖projectiveWeakResolvent V n f‖ ≤ ‖f‖ := by
  change ‖(InnerProductSpace.toDual ℂ (EnergyDomain.Constructions.ProjectiveEnergyDomain V n)).symm
    ((innerSL ℂ f).comp (EnergyDomain.Constructions.projectiveEnergyInclusion V n))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  calc
    ‖(innerSL ℂ f).comp (EnergyDomain.Constructions.projectiveEnergyInclusion V n)‖ ≤
        ‖innerSL ℂ f‖ * ‖EnergyDomain.Constructions.projectiveEnergyInclusion V n‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * 1 := by
      have hf : ‖innerSL ℂ f‖ ≤ ‖f‖ := (innerSL_apply_norm ℂ f).le
      exact mul_le_mul hf (projectiveEnergyInclusion_norm_le_one V n)
        (norm_nonneg (EnergyDomain.Constructions.projectiveEnergyInclusion V n)) (norm_nonneg f)
    _ = ‖f‖ := mul_one _

theorem projectiveWeakResolvent_add (f g : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    projectiveWeakResolvent V n (f + g) = projectiveWeakResolvent V n f + projectiveWeakResolvent V n g := by
  apply ext_inner_right ℂ
  intro v
  rw [projectiveWeakResolvent_pair, inner_add_left, inner_add_left,
    projectiveWeakResolvent_pair, projectiveWeakResolvent_pair]

theorem projectiveWeakResolvent_smul (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) (z : ℂ) :
    projectiveWeakResolvent V n (z • f) = z • projectiveWeakResolvent V n f := by
  apply ext_inner_right ℂ
  intro v
  rw [projectiveWeakResolvent_pair, inner_smul_left (𝕜 := ℂ),
    inner_smul_left (𝕜 := ℂ) (projectiveWeakResolvent V n f) v z, projectiveWeakResolvent_pair]

/-- The actual weak resolvent is a bounded complex-linear operator into the energy domain. -/
def projectiveWeakResolventL : Form.Constructions.ProjectiveL2Forms V (n + 1) →L[ℂ] EnergyDomain.Constructions.ProjectiveEnergyDomain V n :=
  LinearMap.mkContinuous
    { toFun := projectiveWeakResolvent V n
      map_add' := projectiveWeakResolvent_add V n
      map_smul' := fun z f => projectiveWeakResolvent_smul V n f z }
    1 (fun f => by
      change ‖projectiveWeakResolvent V n f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact projectiveWeakResolvent_norm_le V n f)

/-- The bounded L² resolvent of the regularized Hodge equation. -/
def projectiveL2Resolvent : Form.Constructions.ProjectiveL2Forms V (n + 1) →L[ℂ] Form.Constructions.ProjectiveL2Forms V (n + 1) :=
  (EnergyDomain.Constructions.projectiveEnergyInclusion V n).comp (projectiveWeakResolventL V n)

theorem projectiveL2Resolvent_symmetric (f g : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    inner ℂ (projectiveL2Resolvent V n f) g = inner ℂ f (projectiveL2Resolvent V n g) := by
  change inner ℂ (EnergyDomain.Constructions.projectiveEnergyInclusion V n (projectiveWeakResolvent V n f)) g =
    inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n (projectiveWeakResolvent V n g))
  have h := congrArg (starRingEnd ℂ) (projectiveWeakResolvent_pair V n g (projectiveWeakResolvent V n f))
  simp only [inner_conj_symm] at h
  rw [← h, projectiveWeakResolvent_pair]

theorem projectiveL2Resolvent_nonneg (f : Form.Constructions.ProjectiveL2Forms V (n + 1)) :
    0 ≤ (inner ℂ f (projectiveL2Resolvent V n f)).re := by
  change 0 ≤ (inner ℂ f (EnergyDomain.Constructions.projectiveEnergyInclusion V n (projectiveWeakResolvent V n f))).re
  rw [← projectiveWeakResolvent_pair V n f (projectiveWeakResolvent V n f)]
  exact inner_self_nonneg (𝕜 := ℂ) (x := projectiveWeakResolvent V n f)

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakResolvent.Constructions
