import OAI.RepresentationTheory.Weil.UnitarySplitting.WeylResolutionOperator
import OAI.RepresentationTheory.Weil.UnitarySplitting.DiagonalNormGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyCompositionPhase

/-! # Positive Commutation -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation.Construction

noncomputable section

section

/-! Positive normalization of a nonzero operator is unique; the scalar
between two energy-preserving operators is its complex phase. -/

variable {F : Type} [NormedField F] [LocallyCompactSpace F]
variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}

theorem unitary_operator_scalar_norm
    (A B : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hB : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (B f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0) (z : ℂ)
    (hz : A u = z • B u) : ‖z‖ = 1 := by
  have hnA : ‖Weak.Construction.testToL2 F d (A u)‖ = ‖Weak.Construction.testToL2 F d u‖ := by
    rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, hA]
  have hnB : ‖Weak.Construction.testToL2 F d (B u)‖ = ‖Weak.Construction.testToL2 F d u‖ := by
    rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, hB]
  rw [hz, map_smul, norm_smul, hnB] at hnA
  exact mul_right_cancel₀ (norm_ne_zero_iff.mpr (WeylResolutionOperator.Construction.testToL2_ne_zero u hu))
    (hnA.trans (one_mul _).symm)

theorem positive_operator_normalization_unique
    (M : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (A B : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hB : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (B f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hrM : ∀ f, M f = (r : ℂ) • A f) (hsM : ∀ f, M f = (s : ℂ) • B f) :
    r = s ∧ A = B := by
  have hn (U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
      (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f) :
      ‖Weak.Construction.testToL2 F d (U u)‖ = ‖Weak.Construction.testToL2 F d u‖ := by
    rw [Weak.Construction.testToL2_norm, Weak.Construction.testToL2_norm, hU]
  have he := congrArg (fun f => ‖Weak.Construction.testToL2 F d f‖) ((hrM u).symm.trans (hsM u))
  rw [map_smul, map_smul, norm_smul, norm_smul, hn A hA, hn B hB,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hr, abs_of_pos hs] at he
  have hrs : r = s := mul_right_cancel₀ (norm_ne_zero_iff.mpr (WeylResolutionOperator.Construction.testToL2_ne_zero u hu)) he
  refine ⟨hrs, ?_⟩
  apply LinearEquiv.ext
  intro f
  have hh := (hrM f).symm.trans (hsM f)
  rw [← hrs] at hh
  exact smul_right_injective _ (Complex.ofReal_ne_zero.mpr hr.ne') hh

theorem positive_operator_scalar_phase
    (A B : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hB : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (B f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (z : ℂ)
    (heq : ∀ f, (r : ℂ) • A f = (z * (s : ℂ)) • B f) :
    ∀ f, A f = DiagonalNormGaussian.Construction.gaussianPhase z • B f := by
  let a := z * (s : ℂ) / (r : ℂ)
  have ha (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : A f = a • B f := by
    apply smul_right_injective _ (Complex.ofReal_ne_zero.mpr hr.ne')
    dsimp only
    rw [heq, smul_smul]
    congr 1
    dsimp only [a]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  have han := unitary_operator_scalar_norm A B hA hB u hu a (ha u)
  have hphase : a = DiagonalNormGaussian.Construction.gaussianPhase z := by
    have hp : DiagonalNormGaussian.Construction.gaussianPhase a = a := by simp only [DiagonalNormGaussian.Construction.gaussianPhase, han, Complex.ofReal_one, div_one]
    have hmul : (r : ℂ) * a = z * (s : ℂ) := by
      dsimp only [a]
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    have ht := congrArg DiagonalNormGaussian.Construction.gaussianPhase hmul
    rw [DiagonalNormGaussian.Construction.gaussianPhase_mul, DiagonalNormGaussian.Construction.gaussianPhase_mul, DiagonalNormGaussian.Construction.gaussianPhase_positive r hr,
      DiagonalNormGaussian.Construction.gaussianPhase_positive s hs, one_mul, mul_one, hp] at ht
    exact ht
  intro f
  rw [ha, hphase]

end

/-! Symplectic centralizers preserve the Cayley phase, and positive
normalization removes positive scalar commutation factors. -/

theorem cayleyWeylPhase_centralizer
    {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (β : LinearMap.BilinForm F V) (g D k : V ≃ₗ[F] V)
    (hD : ∀ x, D x = g x - x) (hk : ∀ x y, β (k x) (k y) = β x y)
    (hcomm : ∀ x, g (k x) = k (g x)) (x : V) :
    CayleyCompositionPhase.Construction.cayleyWeylPhase β D (k x) = CayleyCompositionPhase.Construction.cayleyWeylPhase β D x := by
  have hDk (v : V) : D (k v) = k (D v) := by rw [hD, hD, map_sub, hcomm]
  have hDi : D.symm (k x) = k (D.symm x) := by
    apply D.injective
    rw [D.apply_symm_apply, hDk, D.apply_symm_apply]
  rw [CayleyCompositionPhase.Construction.cayleyWeylPhase, hDi, hk]
  rfl

theorem positive_operator_commutation
    {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {d : ℕ}
    (M : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (A U : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat F d)
    (hA : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (A f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (hU : ∀ f, Local.FunctionsMetaplectic.Construction.l2Energy F d (U f) = Local.FunctionsMetaplectic.Construction.l2Energy F d f)
    (u : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) (hu : u ≠ 0)
    (r : ℝ) (hr : 0 < r) (hM : ∀ f, M f = (r : ℂ) • A f)
    (c : ℝ) (hc : 0 < c) (hcomm : ∀ f, (c : ℂ) • M (U f) = U (M f)) :
    ∀ f, A (U f) = U (A f) := by
  have he (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) : (c : ℂ) • A (U f) = ((1 : ℂ) * (1 : ℝ)) • U (A f) := by
    have hh := hcomm f
    rw [hM, hM, map_smul, smul_smul, mul_comm, ← smul_smul] at hh
    simpa only [Complex.ofReal_one, one_mul, one_smul] using
      (smul_right_injective _ (Complex.ofReal_ne_zero.mpr hr.ne') hh)
  have hphase := positive_operator_scalar_phase (A.toLinearMap.comp U.toLinearMap)
    (U.toLinearMap.comp A.toLinearMap) (fun f => (hA (U f)).trans (hU f))
    (fun f => (hU (A f)).trans (hA f)) u hu c 1 hc zero_lt_one 1 he
  have h1 : DiagonalNormGaussian.Construction.gaussianPhase (1 : ℂ) = 1 := DiagonalNormGaussian.Construction.gaussianPhase_positive 1 zero_lt_one
  intro f
  have hf := hphase f
  rw [h1, one_smul] at hf
  exact hf

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.PositiveCommutation.Construction
