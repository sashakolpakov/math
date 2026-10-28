import OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.CartanDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.MinkowskiSelfAdjointRealization

/-! # Killing Bracket Cartan Realization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketCartanRealization.Construction

noncomputable section

section

/-! In suitable Euclidean coordinates every automorphism of a real
Killing bracket admits Cartan decomposition. -/

open _root_.ContinuousLinearMap NormedSpace

theorem transported_bracket_adjoint_stable
    {L V : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (B : L →L[ℝ] L →L[ℝ] L) (Φ : L ≃L[ℝ] V)
    (hΦ : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∃ h : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange h B = B ∧
        adjoint (Φ.conjContinuousAlgEquiv g.toContinuousLinearMap) = Φ.conjContinuousAlgEquiv h.toContinuousLinearMap)
    (g : V ≃L[ℝ] V) (hg : ContinuousBracketChange.Construction.continuousBracketChange g (Positive.Killing.Construction.continuousBracketTransport Φ B) = Positive.Killing.Construction.continuousBracketTransport Φ B) :
    ∀ x y, adjoint g.toContinuousLinearMap (Positive.Killing.Construction.continuousBracketTransport Φ B x y) =
      Positive.Killing.Construction.continuousBracketTransport Φ B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y) := by
  let g₀ := (Φ.trans g).trans Φ.symm
  have hconj : (Φ.symm.trans g₀).trans Φ = g := by
    ext x
    simp only [g₀, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.apply_symm_apply]
  have hg₀ : ContinuousBracketChange.Construction.continuousBracketChange g₀ B = B := by
    apply Positive.Killing.Construction.continuousBracketTransport_injective Φ
    rw [Positive.Killing.Construction.continuousBracketTransport_change, hconj]
    exact hg
  obtain ⟨h, hh, hadj⟩ := hΦ g₀ hg₀
  let h' := (Φ.symm.trans h).trans Φ
  have hh' : ContinuousBracketChange.Construction.continuousBracketChange h' (Positive.Killing.Construction.continuousBracketTransport Φ B) = Positive.Killing.Construction.continuousBracketTransport Φ B := by
    rw [← Positive.Killing.Construction.continuousBracketTransport_change, hh]
  have hmap : Φ.conjContinuousAlgEquiv g₀.toContinuousLinearMap = g.toContinuousLinearMap := by
    ext x
    simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g₀,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hmap] at hadj
  change adjoint g.toContinuousLinearMap = h'.toContinuousLinearMap at hadj
  intro x y
  rw [hadj]
  exact (Bracket.PolarDecomposition.Construction.continuousBracketChange_eq_self_iff (Positive.Killing.Construction.continuousBracketTransport Φ B) h').mp hh' x y

theorem exists_killing_bracket_cartan_realization
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : L ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ∀ g : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        ContinuousBracketChange.Construction.continuousBracketChange g (Positive.Killing.Construction.continuousBracketTransport Ψ B) = Positive.Killing.Construction.continuousBracketTransport Ψ B →
        ∃ (k : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
          (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          ContinuousBracketChange.Construction.continuousBracketChange k (Positive.Killing.Construction.continuousBracketTransport Ψ B) = Positive.Killing.Construction.continuousBracketTransport Ψ B ∧
          (∀ x y, inner ℝ (k x) (k y) = inner ℝ x y) ∧ D.toLinearMap.IsSymmetric ∧
          Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (Positive.Killing.Construction.continuousBracketTransport Ψ B) D = 0 ∧
          g.toContinuousLinearMap = k.toContinuousLinearMap * exp D := by
  obtain ⟨m, Ψ, hΨ⟩ := MinkowskiSelfAdjointRealization.Construction.exists_normed_killing_selfAdjoint_realization B hB hK
  refine ⟨m, Ψ, fun g hg => ?_⟩
  exact Bracket.CartanDecomposition.Construction.bracket_automorphism_cartan_decomposition (Positive.Killing.Construction.continuousBracketTransport Ψ B) g hg
    (transported_bracket_adjoint_stable B Ψ hΨ g hg)

end

/-! Adjoint-stable coordinates may be chosen as an automorphism of
the original inner-product space. -/

open _root_.ContinuousLinearMap

theorem exists_killing_selfAdjoint_coordinate_automorphism
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ e : L ≃L[ℝ] L, ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∃ h : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange h B = B ∧
        adjoint (e.conjContinuousAlgEquiv g.toContinuousLinearMap) =
          e.conjContinuousAlgEquiv h.toContinuousLinearMap := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  obtain ⟨Φ, hΦ⟩ := Positive.Killing.Construction.exists_killing_automorphism_selfAdjoint_coordinates B hB hK
  let q := (stdOrthonormalBasis ℝ L).repr.symm
  let e := Φ.trans q.toContinuousLinearEquiv
  refine ⟨e, fun g hg => ?_⟩
  obtain ⟨h, hh, hadj⟩ := hΦ g hg
  refine ⟨h, hh, ?_⟩
  have he := congrArg q.conjStarAlgEquiv hadj
  change q.conjStarAlgEquiv (star (Φ.conjContinuousAlgEquiv g.toContinuousLinearMap)) =
    q.conjStarAlgEquiv (Φ.conjContinuousAlgEquiv h.toContinuousLinearMap) at he
  have he' : adjoint (q.toContinuousLinearEquiv.conjContinuousAlgEquiv
    (Φ.conjContinuousAlgEquiv g.toContinuousLinearMap)) =
      q.toContinuousLinearEquiv.conjContinuousAlgEquiv (Φ.conjContinuousAlgEquiv h.toContinuousLinearMap) :=
    (q.conjStarAlgEquiv.map_star' (Φ.conjContinuousAlgEquiv g.toContinuousLinearMap)).symm.trans he
  exact he'

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketCartanRealization.Construction
