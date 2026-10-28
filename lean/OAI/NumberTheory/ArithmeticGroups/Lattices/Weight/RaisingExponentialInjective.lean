import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Raising Exponential Injective -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponentialInjective.Construction

noncomputable section

/-! Local injectivity of the operator exponential, together with the
contracting split flow, gives injectivity on all weight-raising operators. -/

open scoped Classical _root_.Topology
open Filter NormedSpace

theorem operator_exponential_injective_near_zero
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [CompleteSpace L] :
    ∃ U ∈ 𝓝 (0 : L →L[ℝ] L), Set.InjOn (exp : (L →L[ℝ] L) → (L →L[ℝ] L)) U := by
  let e := ContinuousLinearEquiv.refl ℝ (L →L[ℝ] L)
  have hd : HasStrictFDerivAt exp e.toContinuousLinearMap 0 := hasStrictFDerivAt_exp_zero
  let p := hd.toOpenPartialHomeomorph exp
  exact ⟨p.source, p.open_source.mem_nhds hd.mem_toOpenPartialHomeomorph_source, p.injOn⟩

theorem exponential_injective_on_weightRaising
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    Set.InjOn (exp : (L →L[ℝ] L) → (L →L[ℝ] L)) (Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  obtain ⟨U, hU, hUinj⟩ := operator_exponential_injective_near_zero (L := L)
  intro X hX Y hY hXY
  have hx := (ConjugationContraction.Construction.split_conjugation_contracts_weightRaising b H hH w heig X hX).eventually hU
  have hy := (ConjugationContraction.Construction.split_conjugation_contracts_weightRaising b H hH w heig Y hY).eventually hU
  obtain ⟨t, htX, htY⟩ := (hx.and hy).exists
  have he : exp (exp ((-t) • H) * X * exp (t • H)) =
      exp (exp ((-t) • H) * Y * exp (t • H)) := by
    have h := congrArg (fun Z => exp ((-t) • H) * Z * exp (-((-t) • H))) hXY
    rw [← Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp, ← Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp] at h
    simpa only [neg_smul, neg_neg] using h
  have hconj := hUinj htX htY he
  apply (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv ((-t) • H)).conjContinuousAlgEquiv.injective
  change exp ((-t) • H) * X * exp (-((-t) • H)) =
    exp ((-t) • H) * Y * exp (-((-t) • H))
  simpa only [neg_smul, neg_neg] using hconj

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponentialInjective.Construction
