import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentLocalExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators

/-! # Unipotent Global Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentGlobalExponential.Construction

noncomputable section

/-! The contracting split flow extends local exponential coordinates
to every unipotent bracket automorphism. -/

open scoped Classical _root_.Topology
open Filter NormedSpace _root_.ContinuousLinearMap

theorem bracket_unipotent_is_positive_exponential
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (T : L →L[ℝ] L) (hTB : ∀ x y, T (B x y) = B (T x) (T y))
    (hTW : T - 1 ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w) :
    ∃ X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H, exp X = T := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators b w
  let Z : ℝ → W := fun t => ⟨exp ((-t) • H) * (T - 1) * exp (t • H),
    Weight.ConjugationContraction.Construction.split_conjugation_preserves_weightRaising b H hH.1 w heig t (T - 1) hTW⟩
  have hZlim : Tendsto Z atTop (𝓝 0) := by
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    exact Weight.ConjugationContraction.Construction.split_conjugation_contracts_weightRaising b H hH.1 w heig (T - 1) hTW
  have hInv (t : ℝ) : exp ((-t) • H) * exp (t • H) = 1 := by
    rw [neg_smul, ← exp_add_of_commute (Commute.refl (t • H)).neg_left, neg_add_cancel, exp_zero]
  have hZeq (t : ℝ) : 1 + (Z t).val = exp ((-t) • H) * T * exp (t • H) := by
    change 1 + (exp ((-t) • H) * (T - 1) * exp (t • H)) = _
    rw [mul_sub, sub_mul, mul_one, hInv]
    abel
  have hpres (t : ℝ) : ∀ x y, exp (t • H) (B x y) = B (exp (t • H) x) (exp (t • H) y) := by
    apply Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (t • H)
    apply (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp
    rw [map_smul, hH.2]
    ext x y
    exact smul_zero t
  have hZpres (t : ℝ) : ∀ x y, (1 + (Z t).val) (B x y) =
      B ((1 + (Z t).val) x) ((1 + (Z t).val) y) := by
    intro x y
    rw [hZeq]
    change exp ((-t) • H) (T (exp (t • H) (B x y))) = _
    rw [hpres t, hTB, hpres (-t)]
    rfl
  have hlocal := hZlim.eventually (UnipotentLocalExponential.Construction.unipotent_bracket_local_exponential B b H hH w heig)
  obtain ⟨t, ht⟩ := hlocal.exists
  obtain ⟨X, hXN, hXe⟩ := ht (hZpres t)
  refine ⟨exp (t • H) * X * exp (-(t • H)), ?_, ?_⟩
  · simpa only [neg_neg, neg_smul] using
      Split.ConjugationBracketOperators.Construction.split_conjugation_preserves_positive_derivations B b H hH w heig (-t) X hXN
  · rw [Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp, hXe, hZeq, neg_smul]
    have hi : exp (t • H) * exp (-(t • H)) = 1 := by
      rw [← exp_add_of_commute (Commute.refl (t • H)).neg_right, add_neg_cancel, exp_zero]
    calc
      exp (t • H) * (exp (-(t • H)) * T * exp (t • H)) * exp (-(t • H)) =
          (exp (t • H) * exp (-(t • H))) * T * (exp (t • H) * exp (-(t • H))) := by
        simp only [mul_assoc]
      _ = T := by rw [hi, one_mul, mul_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentGlobalExponential.Construction
