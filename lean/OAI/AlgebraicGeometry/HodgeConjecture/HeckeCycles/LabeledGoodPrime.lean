import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.Completion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting

/-! # Labeled Good Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledGoodPrime.CM

noncomputable section

/-! The actual reduction and its conjugate labels supply every TateComparison
good-prime clause. The denominator condition follows from the residue
map on the original localized ring of integers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (R : M.GoodIntegralReduction q j)

include R in
theorem denominator_coprime : Nat.Coprime q M.arithmetic.denominator := by
  have hu : IsUnit (M.arithmetic.denominator : ZMod q) := by
    simpa only [map_natCast] using M.arithmetic.denominator_isUnit.map R.residue
  exact ((ZMod.isUnit_iff_coprime _ _).mp hu).symm

variable [IsGalois ℚ E]
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ)) (a : M.Family)
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence
    ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))

omit [IsGalois ℚ E] in
theorem completion_apply
    (x : ℤ_[q] ⊗[ℤ] NumberField.RingOfIntegers E) (w : Fin M.s × Bool) :
    (HD).localCompletionMap x w =
      Local.Completion.CM.completionLinear j M.extendedEmbedding x (labels w) := by
  induction x using TensorProduct.inductionOn with
  | tmul b c => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem completion_bijective (hsplit : j.HasSplitCoordinates M.extendedEmbedding) :
    Function.Bijective (HD).localCompletionMap := by
  have h := Local.Completion.CM.completion_bijective j M.extendedEmbedding hsplit
  constructor
  · intro x y hxy
    apply h.1
    funext τ
    obtain ⟨w, rfl⟩ := labels.surjective τ
    simpa only [completion_apply] using congrFun hxy w
  · intro y
    obtain ⟨x, hx⟩ := h.2 (fun τ => y (labels.symm τ))
    refine ⟨x, ?_⟩
    funext w
    rw [completion_apply, hx]
    exact congrArg y (labels.symm_apply_apply w)

include R in
theorem good_prime (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
    (hlabels : ∀ (w : Fin M.s) (b : Bool),
      labels (w, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (w, b)) :
    (HD).IsGoodCompletelySplitPrime := by
  refine ⟨completion_bijective M j labels a C hsplit, ?_, R.levelPrimeToQ a,
    denominator_coprime M j R, ?_⟩
  · intro w b x
    change j.localCharacter M.extendedEmbedding (labels (w, !b)) x =
      j.localCharacter M.extendedEmbedding (labels (w, b))
        (NumberField.IsCMField.ringOfIntegersComplexConj E x)
    rw [hlabels]
    exact (AbelianScheme.FrobeniusKernel.CMPointsCoefficientSplitting.Construction.l45LocalCharacter_conjugation
      j M.extendedEmbedding (labels (w, b)) x).symm
  · exact (Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).mp
      (R.polarizationPrimeToQ a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LabeledGoodPrime.CM
