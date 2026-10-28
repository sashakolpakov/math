import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingSymmetricWeights

/-! # Invariant Form Weight Pairing -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormWeightPairing.Construction

noncomputable section

/-! A nondegenerate invariant bilinear form pairs each simultaneous
weight with its negative. -/

open scoped Classical

theorem invariant_form_weights_opposite
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (a : Submodule ℝ (L →L[ℝ] L)) (b : OrthonormalBasis ι ℝ L)
    (w : ι → Module.Dual ℝ a) (heig : ∀ i (A : a), A.val (b i) = w i A • b i)
    (Q : LinearMap.BilinForm ℝ L) (hQ : Q.Nondegenerate)
    (hinv : ∀ (A : a) x y, Q (A.val x) y + Q x (A.val y) = 0) :
    ∀ i, ∃ j, w j = -w i := by
  intro i
  have hj : ∃ j, Q (b i) (b j) ≠ 0 := by
    by_contra! h
    have hz : Q (b i) = 0 := b.toBasis.ext (fun j => h j)
    have hi : b i = 0 := hQ.1 (b i) (fun y => DFunLike.congr_fun hz y)
    exact b.toBasis.ne_zero i hi
  obtain ⟨j, hj⟩ := hj
  refine ⟨j, ?_⟩
  ext A
  have he := hinv A (b i) (b j)
  rw [heig, heig] at he
  simp only [map_smul, smul_eq_mul] at he
  have hs : w i A + w j A = 0 := (mul_eq_zero.mp (by rwa [add_mul])).resolve_right hj
  change w j A = -(w i A)
  linarith

theorem eigenbasis_weights_separate
    {L ι : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [Fintype ι]
    (a : Submodule ℝ (L →L[ℝ] L)) (b : OrthonormalBasis ι ℝ L)
    (w : ι → Module.Dual ℝ a) (heig : ∀ i (A : a), A.val (b i) = w i A • b i) :
    ∀ A : a, (∀ i, w i A = 0) → A = 0 := by
  intro A hA
  apply Subtype.ext
  have hz : A.val.toLinearMap = 0 := by
    apply b.toBasis.ext
    intro i
    change A.val (b i) = 0
    rw [heig, hA, zero_smul]
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun hz x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantFormWeightPairing.Construction
