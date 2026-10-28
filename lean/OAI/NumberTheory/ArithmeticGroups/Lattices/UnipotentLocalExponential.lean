import OAI.NumberTheory.ArithmeticGroups.Lattices.RestrictedStabilizerLocalImage
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationNilpotence
import OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.LieLocalExponential

/-! # Unipotent Local Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentLocalExponential.Construction

noncomputable section

/-! Every bracket-preserving unipotent operator sufficiently near
the identity is the exponential of a positive derivation. -/

open scoped Classical _root_.Topology
open Filter NormedSpace

theorem unipotent_bracket_local_exponential_within
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (U : Set (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H)) (hU : U ∈ 𝓝 0) :
    ∀ᶠ Z : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w in 𝓝 0,
      (∀ x y, (1 + Z.val) (B x y) = B ((1 + Z.val) x) ((1 + Z.val) y)) →
        ∃ X ∈ U, exp X.val = 1 + Z.val := by
  let : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
  let : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
  let : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let N := DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators b w
  let : NormedAddCommGroup N := inferInstance
  let : NormedSpace ℝ N := inferInstance
  let : FiniteDimensional ℝ N := inferInstance
  have hNW : N ≤ W := Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B b H hH.1 w heig
  let a : N →L[ℝ] W := N.subtypeL.codRestrict W (fun X => hNW X.property)
  have ha : Function.Injective a := by
    intro X Y hXY
    exact Subtype.ext (congrArg (fun Z : W => Z.val) hXY)
  have hrange : a.toLinearMap.range =
      ((Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.comp W.subtype).ker := by
    ext X
    constructor
    · rintro ⟨Y, rfl⟩
      change Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B Y.val = 0
      exact InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _ Y.property
    · intro hX
      have hXN : X.val ∈ N := by
        change X.val ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H
        rw [Positive.DerivationNilpotence.Construction.positiveBracketDerivations_eq_weightRaising B b H hH w heig]
        exact ⟨hX, X.property⟩
      exact ⟨⟨X.val, hXN⟩, rfl⟩
  have hd : HasStrictFDerivAt (fun X : N => exp X.val) (W.subtypeL.comp a) 0 :=
    Minkowski.LieLocalExponential.Construction.hasStrictFDerivAt_exp_linear_zero N.subtypeL
  have hlocal := RestrictedStabilizerLocalImage.Construction.bilinear_stabilizer_local_image_in_submodule_within B W
    (fun X hX Y hY => Weight.RaisingMultiplication.Construction.weightRaisingOperators_mul b w X Y hX hY)
    (fun X : N => exp X.val) a (by simp only [ZeroMemClass.coe_zero, exp_zero]) hd ha hrange
    (fun X => Weight.RaisingExponential.Construction.weightRaising_exp_sub_one_mem b w X.val (hNW X.property))
    (fun X => Bilinear.DerivationExponential.Construction.exp_continuousLinearMap_injective X.val)
    (fun X => Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B X.val
      ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B X.val).mp (InvolutionSpectralDecomposition.Construction.positiveSpectralSubmodule_le _ _ X.property))) U hU
  exact hlocal

theorem unipotent_bracket_local_exponential
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i) :
    ∀ᶠ Z : Positive.DerivationNilpotence.Construction.weightRaisingOperators b w in 𝓝 0,
      (∀ x y, (1 + Z.val) (B x y) = B ((1 + Z.val) x) ((1 + Z.val) y)) →
        ∃ X ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B H, exp X = 1 + Z.val := by
  have h := unipotent_bracket_local_exponential_within B b H hH w heig Set.univ Filter.univ_mem
  filter_upwards [h] with Z hZ
  intro hZB
  obtain ⟨X, _, hX⟩ := hZ hZB
  exact ⟨X.val, X.property, hX⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentLocalExponential.Construction
