import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingBracketCartanRealization
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketAlgebra

/-! # Automorphism Adjoint Derivations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AutomorphismAdjointDerivations.Construction

noncomputable section

/-! Adjoint stability of the bracket automorphism group implies adjoint
stability of its derivations, by differentiating exponential curves. -/

open _root_.ContinuousLinearMap NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracket_derivation_of_exponential_preserves
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L)
    (hA : ∀ t : ℝ, ∀ x y, exp (t • A) (B x y) = B (exp (t • A) x) (exp (t • A) y)) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have heq : (fun t : ℝ => B + Bracket.ChangeDerivative.Construction.continuousBracketExponentialPerturbation B (t • A, 0)) =
      fun _ : ℝ => B := by
    funext t
    rw [Bracket.ExponentialEquiv.Construction.continuousBracketExponentialPerturbation_add, add_zero]
    exact (Bracket.PolarDecomposition.Construction.continuousBracketChange_eq_self_iff B (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv (t • A))).mpr (hA t)
  have hd := Bracket.MinimumStationary.Construction.exponential_bracket_curve_hasDerivAt B A
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const (0 : ℝ) B)

theorem bracket_derivation_adjoint_of_automorphism_adjoint
    (B : L →L[ℝ] L →L[ℝ] L)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (A : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint A) = 0 := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  apply bracket_derivation_of_exponential_preserves
  intro t
  have ht : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (t • A) = 0 := by
    rw [map_smul, hA]
    ext x y
    exact smul_zero t
  have hp := Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (t • A)
    ((OrthogonalBracketAlgebra.Construction.continuousBilinearDerivationDefect_eq_zero_iff B _).mp ht)
  have hg : ContinuousBracketChange.Construction.continuousBracketChange (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv (t • A)) B = B :=
    (Bracket.PolarDecomposition.Construction.continuousBracketChange_eq_self_iff B _).mpr hp
  have h := hadj (Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv (t • A)) hg
  have he : adjoint (exp (t • A)) = exp (t • adjoint A) := by
    change star (exp (t • A)) = _
    rw [star_exp, star_eq_adjoint, map_smul]
  change ∀ x y, adjoint (exp (t • A)) (B x y) =
    B (adjoint (exp (t • A)) x) (adjoint (exp (t • A)) y) at h
  rwa [he] at h

theorem exists_normed_killing_adjoint_stable_realization
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (B : V →L[ℝ] V →L[ℝ] V) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate) :
    ∃ (m : ℕ) (Ψ : V ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      (∀ g : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m),
        ContinuousBracketChange.Construction.continuousBracketChange g (Positive.Killing.Construction.continuousBracketTransport Ψ B) = Positive.Killing.Construction.continuousBracketTransport Ψ B →
        ∀ x y, adjoint g.toContinuousLinearMap (Positive.Killing.Construction.continuousBracketTransport Ψ B x y) =
          Positive.Killing.Construction.continuousBracketTransport Ψ B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y)) ∧
      (∀ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
        Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (Positive.Killing.Construction.continuousBracketTransport Ψ B) A = 0 →
        Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect (Positive.Killing.Construction.continuousBracketTransport Ψ B) (adjoint A) = 0) := by
  obtain ⟨m, Ψ, hΨ⟩ := MinkowskiSelfAdjointRealization.Construction.exists_normed_killing_selfAdjoint_realization B hB hK
  have hadj := KillingBracketCartanRealization.Construction.transported_bracket_adjoint_stable B Ψ hΨ
  exact ⟨m, Ψ, hadj, bracket_derivation_adjoint_of_automorphism_adjoint _ hadj⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AutomorphismAdjointDerivations.Construction
