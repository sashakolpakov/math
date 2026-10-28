import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.ConjugationContraction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential

/-! # Conjugation Bracket Operators -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators.Construction

noncomputable section

section

/-! Split conjugation preserves positive bracket derivations and
commutes with their exponential maps. -/

open _root_.ContinuousLinearMap NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem exponential_conjugation_exp (A X : L →L[ℝ] L) :
    exp (exp A * X * exp (-A)) = exp A * exp X * exp (-A) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  let e := (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv A).conjContinuousAlgEquiv
  have he (Y : L →L[ℝ] L) : e Y = exp A * Y * exp (-A) := rfl
  have hm := map_exp e e.continuous X
  rw [he, he] at hm
  exact hm.symm

theorem split_conjugation_preserves_positive_derivations
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (t : ℝ) (X : L →L[ℝ] L) (hX : X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H) :
    exp ((-t) • H) * X * exp (t • H) ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have hXD : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 := InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _ hX
  have hXW : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w := Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B b H hH.1 w heig hX
  have hHD : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B ((-t) • H) = 0 := by
    rw [map_smul, hH.2]
    ext x y
    exact smul_zero (-t)
  have hpres := Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B ((-t) • H)
    ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp hHD)
  have hd := OrthogonalBracketAlgebra.Construction.bracket_derivation_conjugate B (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv ((-t) • H)) hpres X hXD
  change Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (exp ((-t) • H) * X * exp (-((-t) • H))) = 0 at hd
  rw [Positive.DerivationNilpotence.Construction.positiveBracketDerivations_eq_weightRaising B b H hH w heig]
  refine ⟨?_, Weight.ConjugationContraction.Construction.split_conjugation_preserves_weightRaising b H hH.1 w heig t X hXW⟩
  change Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (exp ((-t) • H) * X * exp (t • H)) = 0
  simpa only [neg_smul, neg_neg] using hd

end

/-! Algebraic identities for split conjugation, including preservation
of bracket automorphisms and the identity-translated weight filtration. -/

open NormedSpace _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem split_exponentials_inverse (H : L →L[ℝ] L) (t : ℝ) :
    exp ((-t) • H) * exp (t • H) = 1 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  rw [neg_smul, ← exp_add_of_commute (Commute.refl (t • H)).neg_left, neg_add_cancel, exp_zero]

theorem split_conjugation_sub_one (H T : L →L[ℝ] L) (t : ℝ) :
    exp ((-t) • H) * T * exp (t • H) - 1 =
      exp ((-t) • H) * (T - 1) * exp (t • H) := by
  rw [mul_sub, sub_mul, mul_one, split_exponentials_inverse]

theorem split_conjugation_inverse (H X : L →L[ℝ] L) (t : ℝ) :
    exp ((-(-t)) • H) * (exp ((-t) • H) * X * exp (t • H)) * exp ((-t) • H) = X := by
  have hi : exp (t • H) * exp ((-t) • H) = 1 := by
    simpa only [neg_neg] using split_exponentials_inverse H (-t)
  rw [neg_neg]
  calc
    _ = (exp (t • H) * exp ((-t) • H)) * X * (exp (t • H) * exp ((-t) • H)) := by
      simp only [mul_assoc]
    _ = X := by rw [hi, one_mul, mul_one]

theorem split_conjugation_preserves_bracket
    (B : L →L[ℝ] L →L[ℝ] L) (H : L →L[ℝ] L)
    (hH : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B H = 0) (t : ℝ)
    (T : L →L[ℝ] L) (hT : ∀ x y, T (B x y) = B (T x) (T y)) :
    ∀ x y, (exp ((-t) • H) * T * exp (t • H)) (B x y) =
      B ((exp ((-t) • H) * T * exp (t • H)) x) ((exp ((-t) • H) * T * exp (t • H)) y) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have hp (s : ℝ) : ∀ x y, exp (s • H) (B x y) = B (exp (s • H) x) (exp (s • H) y) := by
    apply Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (s • H)
    apply (OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp
    rw [map_smul, hH]
    ext x y
    exact smul_zero s
  intro x y
  change exp ((-t) • H) (T (exp (t • H) (B x y))) = _
  rw [hp t, hT, hp (-t)]
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators.Construction
