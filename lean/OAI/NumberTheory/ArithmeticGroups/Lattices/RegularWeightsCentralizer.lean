import OAI.NumberTheory.ArithmeticGroups.Lattices.FaithfulDerivationCommutator
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormWeightPairing
import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularLinearForms

/-! # Regular Weights Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightsCentralizer.Construction

noncomputable section

/-! Regular weights on the underlying Killing Lie algebra determine
the common centralizer of a commuting derivation subspace. -/

open scoped Classical

variable {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [Fintype ι]

omit [FiniteDimensional ℝ L] in
theorem regular_weights_common_kernel
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ A ∈ a, A.toLinearMap.IsSymmetric)
    (b : OrthonormalBasis ι ℝ L) (w : ι → Module.Dual ℝ a)
    (heig : ∀ i (A : a), A.val (b i) = w i A • b i)
    (H : a) (hreg : ∀ i, w i H = 0 ↔ w i = 0)
    (x : L) (hx : H.val x = 0) : ∀ A : a, A.val x = 0 := by
  intro A
  apply b.repr.injective
  ext i
  change b.repr (A.val x) i = b.repr 0 i
  rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b A.val (ha A.val A.property)
    (fun j => w j A) (fun j => heig j A), map_zero, PiLp.zero_apply]
  by_cases hi : w i = 0
  · simp only [hi, LinearMap.zero_apply, zero_mul]
  · have hHi : w i H ≠ 0 := fun hz => hi ((hreg i).mp hz)
    have he := congrArg (fun y => b.repr y i) hx
    rw [CommutingSymmetricWeights.Construction.orthonormal_eigen_coordinate b H.val (ha H.val H.property)
      (fun j => w j H) (fun j => heig j H), map_zero, PiLp.zero_apply] at he
    rw [(mul_eq_zero.mp he).resolve_left hHi, mul_zero]

theorem killing_regular_weights_centralizer
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B)
    (hc : ∀ A ∈ a, ∀ C ∈ a, Commute A C)
    (hmax : ∀ X ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B, (∀ Y ∈ a, Commute X Y) → X ∈ a)
    (b : OrthonormalBasis ι ℝ L) (w : ι → Module.Dual ℝ a)
    (heig : ∀ i (A : a), A.val (b i) = w i A • b i)
    (H : a) (hreg : ∀ i, w i H = 0 ↔ w i = 0) :
    ∀ X ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B, Commute H.val X ↔ X ∈ a := by
  intro X hX
  refine ⟨fun hHX => ?_, fun hXa => hc H.val H.property X hXa⟩
  have hXD : X ∈ (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B).toLinearMap.ker := hX.2
  rw [ContinuousInnerDerivations.Construction.continuousKillingBracket_derivation_kernel B hB hK] at hXD
  obtain ⟨x, hx⟩ := hXD
  change B x = X at hx
  have hHx : H.val x = 0 := by
    apply ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK
    rw [map_zero, ← FaithfulDerivationCommutator.Construction.derivation_commutator_inner_operator B H.val (ha H.property).2 x, hx]
    exact sub_eq_zero.mpr hHX.eq
  have hax := regular_weights_common_kernel a (fun A hA => (ha hA).1) b w heig H hreg x hHx
  apply hmax X hX
  intro A hA
  have he := FaithfulDerivationCommutator.Construction.derivation_commutator_inner_operator B A (ha hA).2 x
  rw [hax ⟨A, hA⟩, map_zero, hx] at he
  exact (sub_eq_zero.mp he).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightsCentralizer.Construction
