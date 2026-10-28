import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousInnerDerivations
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.EuclideanRepresentation

/-! # Cartan Automorphism -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanAutomorphism.Construction

noncomputable section

section

/-! For a Killing bracket whose derivations are stable under adjoints,
the negative adjoint operation lifts uniquely back to the Lie space. -/

open _root_.ContinuousLinearMap

def injectiveLinearLift
    {k E F V : Type*} [Field k] [AddCommGroup E] [Module k E]
    [AddCommGroup F] [Module k F] [AddCommGroup V] [Module k V]
    (f : E →ₗ[k] F) (hf : Function.Injective f) (g : V →ₗ[k] F)
    (hg : g.range ≤ f.range) : V →ₗ[k] E :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp
    (g.codRestrict f.range (fun x => hg ⟨x, rfl⟩))

theorem injectiveLinearLift_apply
    {k E F V : Type*} [Field k] [AddCommGroup E] [Module k E]
    [AddCommGroup F] [Module k F] [AddCommGroup V] [Module k V]
    (f : E →ₗ[k] F) (hf : Function.Injective f) (g : V →ₗ[k] F)
    (hg : g.range ≤ f.range) (x : V) : f (injectiveLinearLift f hf g hg x) = g x := by
  exact congrArg Subtype.val ((LinearEquiv.ofInjective f hf).apply_symm_apply ⟨g x, hg ⟨x, rfl⟩⟩)

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [CompleteSpace L]

def bracketNegativeAdjoint (B : L →L[ℝ] L →L[ℝ] L) : L →ₗ[ℝ] (L →L[ℝ] L) where
  toFun x := -adjoint (B x)
  map_add' x y := by rw [map_add, map_add, neg_add]
  map_smul' c x := by simp only [map_smul, smul_neg, RingHom.id_apply]

theorem bracketNegativeAdjoint_range
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) :
    (bracketNegativeAdjoint B).range ≤ B.toLinearMap.range := by
  rintro _ ⟨x, rfl⟩
  change -adjoint (B x) ∈ B.toLinearMap.range
  apply Submodule.neg_mem
  rw [← ContinuousInnerDerivations.Construction.continuousKillingBracket_derivation_kernel B hB hK]
  apply hAdj
  have hx : B x ∈ B.toLinearMap.range := ⟨x, rfl⟩
  rwa [← ContinuousInnerDerivations.Construction.continuousKillingBracket_derivation_kernel B hB hK] at hx

def continuousBracketCartanMap
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) : L →L[ℝ] L :=
  (injectiveLinearLift B.toLinearMap (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK)
    (bracketNegativeAdjoint B) (bracketNegativeAdjoint_range B hB hK hAdj)).toContinuousLinearMap

theorem continuousBracketCartanMap_adjoint
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) (x : L) :
    B (continuousBracketCartanMap B hB hK hAdj x) = -adjoint (B x) :=
  injectiveLinearLift_apply B.toLinearMap (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK)
    (bracketNegativeAdjoint B) (bracketNegativeAdjoint_range B hB hK hAdj) x

theorem continuousBracketCartanMap_involutive
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) :
    Function.Involutive (continuousBracketCartanMap B hB hK hAdj) := by
  intro x
  apply ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK
  rw [continuousBracketCartanMap_adjoint, continuousBracketCartanMap_adjoint,
    map_neg, adjoint_adjoint, neg_neg]

end

section

/-! The lifted negative adjoint is an involutive automorphism of
the Killing bracket. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [CompleteSpace L]

omit [CompleteSpace L] in
theorem continuousLieBracket_commutator
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (x y : L) :
    B (B x y) = B x * B y - B y * B x := by
  apply ContinuousLinearMap.ext
  intro z
  have he := (ContinuousJacobi.Construction.continuousJacobi_zero_iff B).mp hB.2 x y z
  change B (B x y) z = B x (B y z) - B y (B x z)
  exact eq_sub_of_add_eq (by rw [add_comm]; exact he.symm)

theorem continuousBracketCartanMap_preserves
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) (x y : L) :
    continuousBracketCartanMap B hB hK hAdj (B x y) =
      B (continuousBracketCartanMap B hB hK hAdj x) (continuousBracketCartanMap B hB hK hAdj y) := by
  apply ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK
  rw [continuousBracketCartanMap_adjoint, continuousLieBracket_commutator B hB,
    continuousLieBracket_commutator B hB, continuousBracketCartanMap_adjoint,
    continuousBracketCartanMap_adjoint, map_sub, mul_def, mul_def, adjoint_comp, adjoint_comp]
  rw [neg_mul_neg, neg_mul_neg, neg_sub]
  rfl

def continuousBracketCartanEquiv
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) : L ≃L[ℝ] L :=
  (LinearEquiv.ofBijective (continuousBracketCartanMap B hB hK hAdj).toLinearMap
    (continuousBracketCartanMap_involutive B hB hK hAdj).bijective).toContinuousLinearEquiv

theorem continuousBracketCartanEquiv_apply
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) (x : L) :
    continuousBracketCartanEquiv B hB hK hAdj x = continuousBracketCartanMap B hB hK hAdj x := rfl

theorem continuousBracketCartanEquiv_change
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hAdj : ∀ A, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0) :
    ContinuousBracketChange.Construction.continuousBracketChange (continuousBracketCartanEquiv B hB hK hAdj) B = B := by
  ext x y
  rw [ContinuousBracketChange.Construction.continuousBracketChange_apply]
  change continuousBracketCartanMap B hB hK hAdj
    (B ((continuousBracketCartanEquiv B hB hK hAdj).symm x)
      ((continuousBracketCartanEquiv B hB hK hAdj).symm y)) = B x y
  rw [continuousBracketCartanMap_preserves]
  change B (continuousBracketCartanEquiv B hB hK hAdj
      ((continuousBracketCartanEquiv B hB hK hAdj).symm x))
    (continuousBracketCartanEquiv B hB hK hAdj
      ((continuousBracketCartanEquiv B hB hK hAdj).symm y)) = B x y
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

end

section

/-! The Killing form twisted by the lifted negative adjoint is
symmetric positive definite. -/

open scoped Classical
open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
  [FiniteDimensional ℝ L] [CompleteSpace L]

omit [FiniteDimensional ℝ L] in
theorem continuousOperator_trace_mul_adjoint
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ L) (A C : L →L[ℝ] L) :
    LinearMap.trace ℝ L (A.toLinearMap * (adjoint C).toLinearMap) =
      ∑ i, inner ℝ (C (b i)) (A (b i)) := by
  rw [LinearMap.trace_mul_comm, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (b i) (adjoint C (A (b i))) = _
  rw [adjoint_inner_right]

theorem continuousOperator_trace_mul_adjoint_self_pos
    (A : L →L[ℝ] L) (hA : A ≠ 0) :
    0 < LinearMap.trace ℝ L (A.toLinearMap * (adjoint A).toLinearMap) := by
  let b := stdOrthonormalBasis ℝ L
  have hn : ∃ i, A (b i) ≠ 0 := by
    by_contra! h
    apply hA
    have hz : A.toLinearMap = 0 := b.toBasis.ext (fun i => h i)
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hz x
  rw [continuousOperator_trace_mul_adjoint b]
  simp only [real_inner_self_eq_norm_sq]
  apply Finset.sum_pos'
  · intro i _
    exact sq_nonneg _
  · obtain ⟨i, hi⟩ := hn
    exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hi)⟩

def cartanTwistForm (B : L →L[ℝ] L →L[ℝ] L) (θ : L →L[ℝ] L) : LinearMap.BilinForm ℝ L :=
  -(ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).comp LinearMap.id θ.toLinearMap

omit [CompleteSpace L] in
theorem cartanTwistForm_apply (B : L →L[ℝ] L →L[ℝ] L) (θ : L →L[ℝ] L) (x y : L) :
    cartanTwistForm B θ x y = -ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x (θ y) := rfl

theorem cartanTwistForm_eq_trace (B : L →L[ℝ] L →L[ℝ] L) (θ : L →L[ℝ] L)
    (hθ : ∀ y, B (θ y) = -adjoint (B y)) (x y : L) :
    cartanTwistForm B θ x y = LinearMap.trace ℝ L ((B x).toLinearMap * (adjoint (B y)).toLinearMap) := by
  rw [cartanTwistForm_apply, ContinuousInnerDerivations.Construction.continuousBracketKillingForm_apply, hθ]
  change -LinearMap.trace ℝ L ((B x).toLinearMap * -(adjoint (B y)).toLinearMap) = _
  rw [mul_neg, map_neg, neg_neg]

theorem cartanTwistForm_symmetric (B : L →L[ℝ] L →L[ℝ] L) (θ : L →L[ℝ] L)
    (hθ : ∀ y, B (θ y) = -adjoint (B y)) (x y : L) :
    cartanTwistForm B θ x y = cartanTwistForm B θ y x := by
  let b := stdOrthonormalBasis ℝ L
  rw [cartanTwistForm_eq_trace B θ hθ, cartanTwistForm_eq_trace B θ hθ,
    continuousOperator_trace_mul_adjoint b, continuousOperator_trace_mul_adjoint b]
  apply Finset.sum_congr rfl
  intro i _
  exact real_inner_comm _ _

theorem cartanTwistForm_positive (B : L →L[ℝ] L →L[ℝ] L)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) (θ : L →L[ℝ] L)
    (hθ : ∀ y, B (θ y) = -adjoint (B y)) (x : L) (hx : x ≠ 0) :
    0 < cartanTwistForm B θ x x := by
  rw [cartanTwistForm_eq_trace B θ hθ]
  apply continuousOperator_trace_mul_adjoint_self_pos
  intro h
  exact hx ((injective_iff_map_eq_zero B).mp (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK) x h)

end

section

/-! Every finite-dimensional real Lie bracket with nondegenerate
Killing form admits a Cartan involution. -/

open scoped Classical

theorem exists_killing_bracket_cartan_involution
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ θ : L ≃L[ℝ] L, Function.Involutive θ ∧ ContinuousBracketChange.Construction.continuousBracketChange θ B = B ∧
      ∀ x : L, x ≠ 0 → 0 < -ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x (θ x) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let b := stdOrthonormalBasis ℝ L
  obtain ⟨e, he, hAdj⟩ := EuclideanRepresentation.Construction.exists_killing_bracket_with_adjoint_stable_derivations b B hB hK
  let C := ContinuousBracketChange.Construction.continuousBracketChange e B
  have hC : ContinuousBracketConstraints.Construction.IsContinuousLieBracket C := ContinuousBracketConstraints.Construction.isContinuousLieBracket_change e B hB
  have hKC : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm C).Nondegenerate := by
    apply (KillingDeterminant.Construction.bracketKillingDeterminant_ne_zero b.toBasis C).mp
    rw [show C = ContinuousBracketChange.Construction.continuousBracketChange e B from rfl,
      KillingDeterminant.Construction.bracketKillingDeterminant_change_of_abs_det_one b.toBasis e he B]
    exact (KillingDeterminant.Construction.bracketKillingDeterminant_ne_zero b.toBasis B).mpr hK
  let θ := continuousBracketCartanEquiv C hC hKC hAdj
  have hθ : Function.Involutive θ := continuousBracketCartanMap_involutive C hC hKC hAdj
  have hθC : ContinuousBracketChange.Construction.continuousBracketChange θ C = C := continuousBracketCartanEquiv_change C hC hKC hAdj
  let τ := (e.trans θ).trans e.symm
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x
    change e.symm (θ (e (e.symm (θ (e x))))) = x
    rw [ContinuousLinearEquiv.apply_symm_apply, hθ, ContinuousLinearEquiv.symm_apply_apply]
  · change ContinuousBracketChange.Construction.continuousBracketChange ((e.trans θ).trans e.symm) B = B
    rw [← OrbitMinimum.Construction.continuousBracketChange_trans, ← OrbitMinimum.Construction.continuousBracketChange_trans]
    change ContinuousBracketChange.Construction.continuousBracketChange e.symm (ContinuousBracketChange.Construction.continuousBracketChange θ C) = B
    rw [hθC, ContinuousBracketChange.Construction.continuousBracketChange_inverse]
  · intro x hx
    have hex : e x ≠ 0 := by
      intro h
      apply hx
      apply e.injective
      simpa only [map_zero] using h
    have hp := cartanTwistForm_positive C hKC (continuousBracketCartanMap C hC hKC hAdj)
      (continuousBracketCartanMap_adjoint C hC hKC hAdj) (e x) hex
    rw [cartanTwistForm_apply] at hp
    change 0 < -ContinuousInnerDerivations.Construction.continuousBracketKillingForm C (e x) (θ (e x)) at hp
    have hk := KillingDeterminant.Construction.continuousBracketKillingForm_change e B (e x) (θ (e x))
    change ContinuousInnerDerivations.Construction.continuousBracketKillingForm C (e x) (θ (e x)) =
      ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (e.symm (e x)) (e.symm (θ (e x))) at hk
    rw [ContinuousLinearEquiv.symm_apply_apply] at hk
    rw [hk] at hp
    exact hp

end

/-! A Cartan involution defines a positive bilinear form for which
the adjoint of each bracket automorphism is again a bracket automorphism. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem continuousBracketKillingForm_symmetric
    (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x y = ContinuousInnerDerivations.Construction.continuousBracketKillingForm B y x :=
  LinearMap.trace_mul_comm ℝ _ _

theorem bracketAutomorphism_killing_invariant
    (B : L →L[ℝ] L →L[ℝ] L) (e : L ≃L[ℝ] L) (he : ContinuousBracketChange.Construction.continuousBracketChange e B = B)
    (x y : L) : ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (e x) (e y) = ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x y := by
  have h := KillingDeterminant.Construction.continuousBracketKillingForm_change e B (e x) (e y)
  simpa only [he, ContinuousLinearEquiv.symm_apply_apply] using h

omit [FiniteDimensional ℝ L] in
theorem bracketAutomorphism_inverse
    (B : L →L[ℝ] L →L[ℝ] L) (e : L ≃L[ℝ] L) (he : ContinuousBracketChange.Construction.continuousBracketChange e B = B) :
    ContinuousBracketChange.Construction.continuousBracketChange e.symm B = B := by
  conv_lhs => rw [← he]
  exact ContinuousBracketChange.Construction.continuousBracketChange_inverse e B

omit [FiniteDimensional ℝ L] in
theorem bracketAutomorphism_trans
    (B : L →L[ℝ] L →L[ℝ] L) (e f : L ≃L[ℝ] L)
    (he : ContinuousBracketChange.Construction.continuousBracketChange e B = B) (hf : ContinuousBracketChange.Construction.continuousBracketChange f B = B) :
    ContinuousBracketChange.Construction.continuousBracketChange (e.trans f) B = B := by
  rw [← OrbitMinimum.Construction.continuousBracketChange_trans, he, hf]

def cartanAutomorphismAdjoint (θ e : L ≃L[ℝ] L) : L ≃L[ℝ] L := (θ.trans e.symm).trans θ

omit [FiniteDimensional ℝ L] in
theorem cartanAutomorphismAdjoint_preserves
    (B : L →L[ℝ] L →L[ℝ] L) (θ e : L ≃L[ℝ] L)
    (hθ : ContinuousBracketChange.Construction.continuousBracketChange θ B = B) (he : ContinuousBracketChange.Construction.continuousBracketChange e B = B) :
    ContinuousBracketChange.Construction.continuousBracketChange (cartanAutomorphismAdjoint θ e) B = B :=
  bracketAutomorphism_trans B (θ.trans e.symm) θ
    (bracketAutomorphism_trans B θ e.symm hθ (bracketAutomorphism_inverse B e he)) hθ

theorem cartanTwistForm_automorphism_adjoint
    (B : L →L[ℝ] L →L[ℝ] L) (θ e : L ≃L[ℝ] L) (hθ : Function.Involutive θ)
    (he : ContinuousBracketChange.Construction.continuousBracketChange e B = B) (x y : L) :
    cartanTwistForm B θ.toContinuousLinearMap (e x) y =
      cartanTwistForm B θ.toContinuousLinearMap x (cartanAutomorphismAdjoint θ e y) := by
  rw [cartanTwistForm_apply, cartanTwistForm_apply]
  change -ContinuousInnerDerivations.Construction.continuousBracketKillingForm B (e x) (θ y) =
    -ContinuousInnerDerivations.Construction.continuousBracketKillingForm B x (θ (θ (e.symm (θ y))))
  rw [hθ]
  have h := bracketAutomorphism_killing_invariant B e he x (e.symm (θ y))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using congrArg Neg.neg h

theorem cartanTwistForm_symmetric_of_involution
    (B : L →L[ℝ] L →L[ℝ] L) (θ : L ≃L[ℝ] L) (hθ : Function.Involutive θ)
    (hpres : ContinuousBracketChange.Construction.continuousBracketChange θ B = B) (x y : L) :
    cartanTwistForm B θ.toContinuousLinearMap x y = cartanTwistForm B θ.toContinuousLinearMap y x := by
  rw [cartanTwistForm_apply, cartanTwistForm_apply]
  have h := bracketAutomorphism_killing_invariant B θ hpres x (θ y)
  rw [hθ, continuousBracketKillingForm_symmetric B (θ x) y] at h
  exact congrArg Neg.neg h.symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanAutomorphism.Construction
