import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConormalEigenquotient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRanks

/-! # Lie Rank Quotient Criterion -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankQuotientCriterion.AlgebraicLie

noncomputable section

/-! Finite integral-basis equations identify the original Lie-rank
predicate with the dimension of an equivariantly identified conormal quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable
    {E k B P : Type} [Field E] [NumberField E] [Field k] [CommRing B] [Algebra B k]
    [AddCommGroup P] [Module B P] [Module.Finite B P] {g : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (τ : NumberField.RingOfIntegers E →+* k)
    (d : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → Module.End B P)
    (t : Fin (Module.finrank ℤ (NumberField.RingOfIntegers E)) → B)
    (e : LiePoints.AlgebraicLie.Space A.scheme ≃ₗ[k] (P →ₗ[B] k))
    (he : ∀ i v, e (LieAlgebraic.AlgebraicLie.map (ρ.map (IntegralModel.Finite.Actions.integralActionBasis E i)) v) = (e v).comp (d i))
    (hτ : ∀ i, τ (IntegralModel.Finite.Actions.integralActionBasis E i) = algebraMap B k (t i))

private theorem eigenspace_eq_joint : LieEigenspaces.AlgebraicLie.eigenspace A ρ τ =
    ConormalEigenquotient.jointEigenspace (fun i => LieAlgebraic.AlgebraicLie.map (ρ.map (IntegralModel.Finite.Actions.integralActionBasis E i)))
      (fun i => τ (IntegralModel.Finite.Actions.integralActionBasis E i)) := by
  apply Submodule.ext
  intro v
  exact (Integral.LieEquations.AlgebraicLie.mem_eigenspace_iff_basis A ρ τ v).trans
    (ConormalEigenquotient.mem_jointEigenspace_iff _ _ v).symm

include e he hτ in
private theorem eigenspace_finrank_quotient :
    Module.finrank k (LieEigenspaces.AlgebraicLie.eigenspace A ρ τ) =
      Module.finrank k (k ⊗[B] ConormalEigenquotient.conormalEigenquotient d t) := by
  have hE := eigenspace_eq_joint A ρ τ
  exact (LinearEquiv.ofEq _ _ hE).finrank_eq.trans
    (ConormalEigenquotient.jointEigenspace_finrank_conormal_quotient _ _ d t e he hτ)

include e he hτ in
theorem hasLieRank_iff_conormal_quotient (r : ℕ) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r ↔ Module.finrank k (k ⊗[B] ConormalEigenquotient.conormalEigenquotient d t) = r := by
  rw [LieRanks.AlgebraicLie.hasLieRank_iff_finrank A ρ τ r, eigenspace_finrank_quotient A ρ τ d t e he hτ]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieRankQuotientCriterion.AlgebraicLie
