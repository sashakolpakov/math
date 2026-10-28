import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
import OAI.RepresentationTheory.Weil.Local.Gaussian

/-! # Real Test Space -/

namespace OAI.RepresentationTheory.Weil.Local.RealTestSpace.Construction

noncomputable section

/-! Identification with the real Schwartz space and stability under quadratic phases. -/

open scoped SchwartzMap ContDiff

theorem locallyConstant_contDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : IsLocallyConstant f) : ContDiff ℝ ∞ f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_const.congr_of_eventuallyEq (hf.eventually_eq x)

theorem schwartzBruhat_real_iff {n : ℕ} {f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ} :
    f ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℝ n ↔ ∃ φ : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ, f = φ := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        rcases hf with hf | ⟨d, e, φ, rfl⟩
        · exact ⟨hf.2.toSchwartzMap (locallyConstant_contDiff hf.1), rfl⟩
        · let a := e.symm.toAddEquiv.toRealLinearEquiv
            e.symm.continuous e.continuous
          exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ a φ, rfl⟩
    | zero => exact ⟨0, rfl⟩
    | add f g _ _ hf hg =>
        obtain ⟨φ, rfl⟩ := hf
        obtain ⟨χ, rfl⟩ := hg
        exact ⟨φ + χ, rfl⟩
    | smul c f _ hf =>
        obtain ⟨φ, rfl⟩ := hf
        exact ⟨c • φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    exact FunctionsMetaplectic.Construction.schwartz_coordinate_mem (ContinuousAddEquiv.refl _) φ

def realSchwartzToBruhat {n : ℕ} :
    SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℝ n where
  toFun f := ⟨f, schwartzBruhat_real_iff.mpr ⟨f, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realSchwartzToBruhat_bijective {n : ℕ} :
    Function.Bijective (realSchwartzToBruhat (n := n)) := by
  constructor
  · intro f g h
    exact DFunLike.ext' (congrArg Subtype.val h)
  · intro f
    obtain ⟨φ, hφ⟩ := schwartzBruhat_real_iff.mp f.property
    exact ⟨φ, Subtype.ext hφ.symm⟩

def realSchwartzEquiv (n : ℕ) :
    SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  LinearEquiv.ofBijective realSchwartzToBruhat realSchwartzToBruhat_bijective

theorem realSchwartzEquiv_apply {n : ℕ}
    (f : SchwartzMap (FunctionsMetaplectic.Construction.Position ℝ n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (realSchwartzEquiv n f).val x = f x := rfl

theorem realSchwartzEquiv_symm_apply {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (realSchwartzEquiv n).symm f x = f.val x := by
  have h := congrArg (fun g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n => g.val x)
    ((realSchwartzEquiv n).apply_symm_apply f)
  exact h

def unitPhaseExp (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem unitPhaseExp_hasDerivAt (t : ℝ) :
    HasDerivAt unitPhaseExp (unitPhaseExp t * Complex.I) t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).mul_const Complex.I
  exact h.cexp

theorem unitPhaseExp_iteratedDeriv (n : ℕ) :
    iteratedDeriv n unitPhaseExp = fun t => Complex.I ^ n * unitPhaseExp t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((unitPhaseExp_hasDerivAt t).const_mul (Complex.I ^ n)).deriv]
      rw [pow_succ]
      ring

theorem unitPhaseExp_temperate : Function.HasTemperateGrowth unitPhaseExp := by
  refine ⟨?_, fun n => ⟨0, 1, fun t => ?_⟩⟩
  · exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, unitPhaseExp_iteratedDeriv]
    simp [unitPhaseExp, norm_pow, Complex.norm_exp]

theorem realCharacter_temperate (c : ℝ) :
    Function.HasTemperateGrowth (Gaussian.Construction.realCharacter c) := by
  have h : (Gaussian.Construction.realCharacter c : ℝ → ℂ) = unitPhaseExp ∘ (fun t => 2 * Real.pi * c * t) := by
    funext t
    exact Gaussian.Construction.realCharacter_apply c t
  rw [h]
  exact unitPhaseExp_temperate.comp ((Function.HasTemperateGrowth.const _).mul .id)

theorem quadratic_real_temperate {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    Function.HasTemperateGrowth (FunctionsMetaplectic.Construction.quadratic B) := by
  have hc (i : Fin n) : Function.HasTemperateGrowth (fun x : FunctionsMetaplectic.Construction.Position ℝ n => x i) :=
    (ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position ℝ n →L[ℝ] ℝ).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth
      (fun x : FunctionsMetaplectic.Construction.Position ℝ n => ∑ i, ∑ j, x i * B i j * x j) :=
    .sum (fun i _ => .sum (fun j _ => ((hc i).mul (.const (B i j))).mul (hc j)))
  exact hq.mul (.const (2 : ℝ)⁻¹)

theorem quadraticOperator_real_mem {n : ℕ} (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ)
    {f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ} (hf : f ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) B f ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := by
  obtain ⟨φ, rfl⟩ := schwartzBruhat_real_iff.mp hf
  let χ := SchwartzMap.smulLeftCLM ℂ (fun x => Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic B x)) φ
  refine schwartzBruhat_real_iff.mpr ⟨χ, ?_⟩
  funext x
  exact (SchwartzMap.smulLeftCLM_apply_apply
    ((realCharacter_temperate c).comp (quadratic_real_temperate B)) φ x).symm

end

end OAI.RepresentationTheory.Weil.Local.RealTestSpace.Construction
