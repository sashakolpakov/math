import OAI.RepresentationTheory.Weil.AdelicSplitting.Rational
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Rational Levi -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi.Construction

noncomputable section

/-! Actual normalized rational Levi lifts and their finite-place vacua. -/

open _root_.MeasureTheory
open scoped Classical _root_.NumberField BigOperators

open OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

instance completionSecondCountableTopology (v : ArchimedeanAdeles.Construction.Places F) :
    SecondCountableTopology (ArchimedeanAdeles.Construction.Completion F v) := by
  cases v with
  | inl v =>
      let : NontriviallyNormedField v.Completion :=
        { (inferInstance : NormedField v.Completion) with
          non_trivial := ⟨algebraMap F v.Completion 2, by
            change 1 < ‖((WithAbs.equiv v.1).symm (2 : F) : v.Completion)‖
            rw [NumberField.InfinitePlace.Completion.norm_coe]
            change 1 < v (2 : F)
            rw [show (2 : F) = (2 : ℕ) from rfl, v.map_natCast]
            norm_num⟩ }
      let : ProperSpace v.Completion :=
        ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace v.Completion
      infer_instance
  | inr v => infer_instance

theorem positive_scalar_eigenvector
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    {N : ℕ} {ψ : AddChar k ℂ} (T : Oscillator.Construction.LocalCover k N ψ)
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) (hf : f ≠ 0) (c : ℝ) (hc : 0 < c)
    (he : Oscillator.Construction.localOperator k N ψ T f = (c : ℂ) • f) : c = 1 := by
  have hE : Local.FunctionsMetaplectic.Construction.l2Energy k N f ≠ 0 := by
    exact (TestSpace.LocalAnalysis.schwartzBruhat_integral_norm_sq_eq_zero_iff
      (Measure.pi (fun _ : Fin N => (Measure.addHaar : Measure k))) f).not.mpr hf
  have h := T.property.1 f
  change Local.FunctionsMetaplectic.Construction.l2Energy k N (Oscillator.Construction.localOperator k N ψ T f) = Local.FunctionsMetaplectic.Construction.l2Energy k N f at h
  rw [he] at h
  have hscale : Local.FunctionsMetaplectic.Construction.l2Energy k N ((c : ℂ) • f) = c ^ 2 * Local.FunctionsMetaplectic.Construction.l2Energy k N f := by
    unfold Local.FunctionsMetaplectic.Construction.l2Energy
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
    exact integral_const_mul _ _
  rw [hscale] at h
  have hc2 : c ^ 2 = 1 := mul_right_cancel₀ hE (h.trans (one_mul _).symm)
  nlinarith

theorem finitePositionLattice_mulVec
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (A : Matrix (Fin N) (Fin N) (v.adicCompletion F))
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F)
    {x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N} (hx : x ∈ Vacuum.Construction.finitePositionLattice F N v) :
    A.mulVec x ∈ Vacuum.Construction.finitePositionLattice F N v := by
  intro i _
  apply (v.adicCompletionIntegers F).sum_mem
  intro j _
  exact (v.adicCompletionIntegers F).toSubring.mul_mem (hA i j) (hx j (Set.mem_univ j))

theorem finiteVacuum_substitution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (A : Local.FunctionsMetaplectic.Construction.GeneralLinear (v.adicCompletion F) N)
    (hA : ∀ i j, A.val i j ∈ v.adicCompletionIntegers F)
    (hAi : ∀ i j, (A⁻¹).val i j ∈ v.adicCompletionIntegers F)
    (x : Local.FunctionsMetaplectic.Construction.Position (v.adicCompletion F) N) :
    (Vacuum.Construction.finiteVacuum F N v).val ((A⁻¹).val.mulVec x) = (Vacuum.Construction.finiteVacuum F N v).val x := by
  have hi : (A⁻¹).val.mulVec x ∈ Vacuum.Construction.finitePositionLattice F N v ↔
      x ∈ Vacuum.Construction.finitePositionLattice F N v := by
    constructor
    · intro hx
      have h := finitePositionLattice_mulVec F N v A.val hA hx
      simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mulVec] using h
    · exact finitePositionLattice_mulVec F N v (A⁻¹).val hAi
  change (Vacuum.Construction.finitePositionLattice F N v).indicator (fun _ => (1 : ℂ))
      ((A⁻¹).val.mulVec x) = (Vacuum.Construction.finitePositionLattice F N v).indicator (fun _ => (1 : ℂ)) x
  simp only [Set.indicator_apply, hi]

theorem finite_linearOscillator_fixes_vacuum
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (ψ : AddChar (v.adicCompletion F) ℂ) (A : Local.FunctionsMetaplectic.Construction.GeneralLinear (v.adicCompletion F) N)
    (hA : ∀ i j, A.val i j ∈ v.adicCompletionIntegers F)
    (hAi : ∀ i j, (A⁻¹).val i j ∈ v.adicCompletionIntegers F) :
    Oscillator.Construction.localOperator (v.adicCompletion F) N ψ (NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A) (Vacuum.Construction.finiteVacuum F N v) =
      Vacuum.Construction.finiteVacuum F N v := by
  let c := LinearSubstitution.LocalAnalysis.coordinateScale (LinearSubstitution.LocalAnalysis.positionAddEquiv A)
  have he : Oscillator.Construction.localOperator (v.adicCompletion F) N ψ (NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A)
      (Vacuum.Construction.finiteVacuum F N v) = (c : ℂ) • Vacuum.Construction.finiteVacuum F N v := by
    apply Subtype.ext
    funext x
    change (c : ℂ) * (Vacuum.Construction.finiteVacuum F N v).val ((A⁻¹).val.mulVec x) =
      (c : ℂ) * (Vacuum.Construction.finiteVacuum F N v).val x
    rw [finiteVacuum_substitution F N v A hA hAi]
  have hf : Vacuum.Construction.finiteVacuum F N v ≠ 0 := by
    intro h
    have hz := Vacuum.Construction.finiteVacuum_zero F N v
    rw [h] at hz
    exact zero_ne_one hz
  have hc := positive_scalar_eigenvector (NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator ψ A) (Vacuum.Construction.finiteVacuum F N v)
    hf c (LinearSubstitution.LocalAnalysis.coordinateScale_pos (LinearSubstitution.LocalAnalysis.positionAddEquiv A)) he
  simpa only [hc, Complex.ofReal_one, one_smul] using he

variable (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

def rationalLeviLocal (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : ArchimedeanAdeles.Construction.Places F) : Vacuum.Construction.CoverAt F N ψ v :=
  NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator (Characters.Construction.localAdditiveCharacter F ψ v) (Rational.Construction.localizeLinear F N A v)

theorem rationalLeviLocal_covers (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) (v : ArchimedeanAdeles.Construction.Places F) :
    Vacuum.Construction.projectionAt F N ψ v (rationalLeviLocal F N ψ A v) =
      Vacuum.Construction.rationalSymplecticLocal F N v (Local.Generators.Construction.leviSymplectic A) := by
  apply Subtype.ext
  ext i j
  cases i <;> cases j <;>
    simp [rationalLeviLocal, Vacuum.Construction.projectionAt, Oscillator.Construction.localProjection, NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator,
      Rational.Construction.localizeLinear, Vacuum.Construction.rationalSymplecticLocal, Vacuum.Construction.mapSymplectic, Local.Generators.Construction.leviSymplectic, Matrix.fromBlocks]

theorem localizeLinear_integral (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    ∀ᶠ v in Filter.cofinite,
      (∀ i j, (Rational.Construction.localizeLinear F N A v).val i j ∈ Integral.Construction.localIntegerRing F v) ∧
      (∀ i j, ((Rational.Construction.localizeLinear F N A v)⁻¹).val i j ∈ Integral.Construction.localIntegerRing F v) := by
  have hA : ∀ᶠ v in Filter.cofinite, ∀ i j,
      ArchimedeanAdeles.Construction.rationalScalar F v (A.val i j) ∈ Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Integral.Construction.rationalScalar_integral F (A.val i j)
  have hAi : ∀ᶠ v in Filter.cofinite, ∀ i j,
      ArchimedeanAdeles.Construction.rationalScalar F v ((A⁻¹).val i j) ∈ Integral.Construction.localIntegerRing F v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      Integral.Construction.rationalScalar_integral F ((A⁻¹).val i j)
  exact hA.and hAi

theorem rationalLeviLocal_integral (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    ∀ᶠ v in Filter.cofinite, rationalLeviLocal F N ψ A v ∈ Vacuum.Construction.coverIntegral F N ψ v := by
  filter_upwards [Vacuum.Construction.rationalSymplecticLocal_integral F N (Local.Generators.Construction.leviSymplectic A),
    localizeLinear_integral F N A] with v hp hA
  refine ⟨?_, ?_⟩
  · change Vacuum.Construction.projectionAt F N ψ v (rationalLeviLocal F N ψ A v) ∈ Vacuum.Construction.symplecticIntegral F N v
    rwa [rationalLeviLocal_covers]
  · cases v with
    | inl v => trivial
    | inr v =>
        let : MeasurableSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
        let : BorelSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionBorelSpace F (.inr v)
        exact finite_linearOscillator_fixes_vacuum F N v (Characters.Construction.localAdditiveCharacter F ψ (.inr v))
          (Rational.Construction.localizeLinear F N A (.inr v)) hA.1 hA.2

def rationalLeviFamily (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) : Rational.Construction.RestrictedCover F N ψ :=
  ⟨rationalLeviLocal F N ψ A, rationalLeviLocal_integral F N ψ A⟩

theorem rationalLeviFamily_spec (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    Rational.Construction.IsRationalLevi F N ψ A (rationalLeviFamily F N ψ A) := by
  constructor
  · exact rationalLeviLocal_covers F N ψ A
  · intro v f x
    exact NonarchimedeanIntertwiner.LocalAnalysis.linearOscillator_apply (Characters.Construction.localAdditiveCharacter F ψ v) (Rational.Construction.localizeLinear F N A v) f x

theorem rationalGraph_contains_levi (A : Local.FunctionsMetaplectic.Construction.GeneralLinear F N) :
    (Local.Generators.Construction.leviSymplectic A, Rational.Construction.assembleGlobalCover F N ψ (rationalLeviFamily F N ψ A)) ∈
      Rational.Construction.rationalGraph F N ψ :=
  Subgroup.subset_closure (Or.inl ⟨A, rationalLeviFamily F N ψ A,
    rationalLeviFamily_spec F N ψ A, rfl⟩)

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RationalLevi.Construction
