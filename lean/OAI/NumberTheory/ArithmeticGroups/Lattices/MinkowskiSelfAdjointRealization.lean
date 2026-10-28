import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.Killing

/-! # Minkowski Self Adjoint Realization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MinkowskiSelfAdjointRealization.Construction

noncomputable section

section

/-! Self-adjoint Euclidean realizations also apply to Killing brackets
on finite-dimensional normed spaces without a chosen inner product. -/

open _root_.ContinuousLinearMap

theorem exists_normed_killing_selfAdjoint_realization
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : L ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
        ∃ h : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange h B = B ∧
          adjoint (Ψ.conjContinuousAlgEquiv g.toContinuousLinearMap) =
            Ψ.conjContinuousAlgEquiv h.toContinuousLinearMap := by
  let n := Module.finrank ℝ L
  let e : L ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((Module.finBasis ℝ L).equivFun.trans
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm).toContinuousLinearEquiv
  let C := Positive.Killing.Construction.continuousBracketTransport e B
  have hC : ContinuousBracketConstraints.Construction.IsContinuousLieBracket C := Positive.Killing.Construction.continuousBracketTransport_isLie e B hB
  have hKC : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm C).Nondegenerate :=
    Positive.Killing.Construction.continuousBracketTransport_killing_nondegenerate e B hK
  obtain ⟨Φ, hΦ⟩ := Positive.Killing.Construction.exists_killing_automorphism_selfAdjoint_coordinates C hC hKC
  refine ⟨Module.finrank ℝ (EuclideanSpace ℝ (Fin n)), e.trans Φ, fun g hg => ?_⟩
  let g' := (e.symm.trans g).trans e
  have hg' : ContinuousBracketChange.Construction.continuousBracketChange g' C = C := by
    change ContinuousBracketChange.Construction.continuousBracketChange ((e.symm.trans g).trans e) (Positive.Killing.Construction.continuousBracketTransport e B) = _
    rw [← Positive.Killing.Construction.continuousBracketTransport_change, hg]
  obtain ⟨h', hh', hadj⟩ := hΦ g' hg'
  let h := (e.trans h').trans e.symm
  have hconj : (e.symm.trans h).trans e = h' := by
    ext x
    simp only [h, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hh : ContinuousBracketChange.Construction.continuousBracketChange h B = B := by
    apply Positive.Killing.Construction.continuousBracketTransport_injective e
    rw [Positive.Killing.Construction.continuousBracketTransport_change, hconj]
    exact hh'
  refine ⟨h, hh, ?_⟩
  have hmap : e.conjContinuousAlgEquiv h.toContinuousLinearMap = h'.toContinuousLinearMap := by
    ext x
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, h,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_trans]
  change adjoint (Φ.conjContinuousAlgEquiv g'.toContinuousLinearMap) =
    Φ.conjContinuousAlgEquiv (e.conjContinuousAlgEquiv h.toContinuousLinearMap)
  rw [hmap]
  exact hadj

end

/-! The actual real Minkowski Lie algebra of a connected semisimple
group has a self-adjoint Euclidean realization of its automorphisms. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.ContinuousLinearMap

local instance lieMixedSpan_normed_uniform_for_selfAdjoint
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    UniformSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace

local instance lieMixedSpan_normed_topology_for_selfAdjoint
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    TopologicalSpace (Lie.MixedLattice.Construction.lieMixedSpan G) :=
  (inferInstance : NormedAddCommGroup (Lie.MixedLattice.Construction.lieMixedSpan G)).toUniformSpace.toTopologicalSpace

theorem lieMixedContinuousBracket_isLie
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) :
    ContinuousBracketConstraints.Construction.IsContinuousLieBracket (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) := by
  constructor
  · intro x
    exact lie_self (L := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG) x
  · apply (ContinuousJacobi.Construction.continuousJacobi_zero_iff _).mpr
    intro x y z
    have h := LieRing.leibniz_lie (L := Lie.DerivationDefect.Construction.lieMixedRealSubalgebra G hG) x y z
    exact h.trans (add_comm _ _)

theorem lieMixedContinuousBracket_killing_nondegenerate
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    (ContinuousInnerDerivations.Construction.continuousBracketKillingForm (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG)).Nondegenerate := by
  have hform : ContinuousInnerDerivations.Construction.continuousBracketKillingForm (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) =
      Minkowski.KillingForm.Construction.lieMixedKillingForm G hG := by ext x y; rfl
  rw [hform]
  exact Minkowski.KillingForm.Construction.lieMixedKillingForm_nondegenerate G hG hsemi

theorem lieMixed_selfAdjoint_realization
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    ∃ (m : ℕ) (Ψ : Lie.MixedLattice.Construction.lieMixedSpan G ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ∀ g : Lie.MixedLattice.Construction.lieMixedSpan G ≃L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G,
        ContinuousBracketChange.Construction.continuousBracketChange g (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) = Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG →
        ∃ h : Lie.MixedLattice.Construction.lieMixedSpan G ≃L[ℝ] Lie.MixedLattice.Construction.lieMixedSpan G,
          ContinuousBracketChange.Construction.continuousBracketChange h (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG) = Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG ∧
          adjoint (Ψ.conjContinuousAlgEquiv g.toContinuousLinearMap) =
            Ψ.conjContinuousAlgEquiv h.toContinuousLinearMap :=
  exists_normed_killing_selfAdjoint_realization (Minkowski.LieTangent.Construction.lieMixedContinuousBracket G hG)
    (lieMixedContinuousBracket_isLie G hG) (lieMixedContinuousBracket_killing_nondegenerate G hG hsemi)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MinkowskiSelfAdjointRealization.Construction
