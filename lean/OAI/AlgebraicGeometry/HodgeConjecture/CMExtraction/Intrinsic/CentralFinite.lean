import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparisonCompletion
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrder
import OAI.NumberTheory.ClassGroup.Finiteness

/-! # Central Finite -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite

noncomputable section

/-! The complete proved CentralAction applies to every action returned by GeometricTheta,
using TateComparison geometric uniqueness to recover its full conclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.CentralAction.FiniteOrder.Construction

theorem verifiedFiniteness (E : Type*) [Field E] [NumberField E] : AbelianScheme.CentralAction.Arithmetic.Construction.PrincipalizationInput E :=
  NumberTheory.ClassGroup.Finiteness.fractionalIdeal_pow_principal E

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
  (hq : D.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.RealizesIsogenyQuotient)

/-- Finite order on the actual full Albanese and Betti cohomology, with
one exponent and the geometric graph witnesses retained. -/
theorem native_central_actions_finite_order
    (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (active : Fin s) (fullSide : Fin s → Bool) :
    ∃ (σT σC : Aut D.space),
      AbelianScheme.CentralAction.Interface.Construction.CorrespondenceIsGraph (D.correspondence (AbelianScheme.CentralAction.CentralRepresentatives.Construction.clearedT3Type active)) (σT ≪≫ A.shift) ∧
      AbelianScheme.CentralAction.Interface.Construction.CorrespondenceIsGraph (D.correspondence (AbelianScheme.CentralAction.CentralRepresentatives.Construction.c0IntegralType active fullSide)) σC ∧
      ∃ n : ℕ, 0 < n ∧ σT ^ n = 1 ∧ σC ^ n = 1 ∧
        (A.algebraAction (AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
        (A.algebraAction (AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 ∧
        (A.cohomologyAction (AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
        (A.cohomologyAction (AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 := by
  obtain ⟨coeff, hfull⟩ := TateComparisonCompletion.Intrinsic.native_action_full_conclusion D hg hq hIsogenyQuotient hTateComparison A hA
  exact AbelianScheme.CentralAction.FiniteOrder.Construction.central_hecke_actions_finite_order s hdegree q D hg hq hIsogenyQuotient active fullSide
    (TateComparisonCompletion.Intrinsic.fullNativeAction D A coeff) hfull (verifiedFiniteness E)

/-- Scalar extension of the actual full rational Hecke action. -/
def nativeFullHeckeActionOver (F : Type*) [Field F] [Algebra ℚ F] (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) :
    F ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[F] Module.End F (F ⊗[ℚ] D.H1) :=
  AlgHom.liftEquiv ℚ F (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) (Module.End F (F ⊗[ℚ] D.H1))
    ((Module.End.baseChangeHom ℚ F D.H1).comp A.cohomologyAction)

theorem nativeFullHeckeActionOver_tmul (F : Type*) [Field F] [Algebra ℚ F]
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (c : F) (h : AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :
    nativeFullHeckeActionOver D F A (c ⊗ₜ[ℚ] h) = c • (A.cohomologyAction h).baseChange F := rfl

/-- The exact central finite-order premise of CentralConstraint after coefficient extension. -/
theorem native_central_actions_over_finite_order
    (hdegree : Module.finrank ℚ E = 2 * s)
    (hTateComparison : RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonOutput D hg hq hIsogenyQuotient)
    (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D) (hA : A.IsRealization D hg hq hIsogenyQuotient)
    (active : Fin s) (fullSide : Fin s → Bool)
    (F : Type*) [Field F] [Algebra ℚ F] :
    ∃ n : ℕ, 0 < n ∧
      (nativeFullHeckeActionOver D F A (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q active)) ^ n = 1 ∧
      (nativeFullHeckeActionOver D F A (1 ⊗ₜ[ℚ] AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q active fullSide)) ^ n = 1 := by
  obtain ⟨_, _, _, _, n, hn, _, _, _, _, hT, hC⟩ :=
    native_central_actions_finite_order D hg hq hIsogenyQuotient hdegree hTateComparison A hA active fullSide
  refine ⟨n, hn, ?_, ?_⟩
  · rw [nativeFullHeckeActionOver_tmul, one_smul, ← LinearMap.baseChange_pow, hT,
      LinearMap.baseChange_one]
  · rw [nativeFullHeckeActionOver_tmul, one_smul, ← LinearMap.baseChange_pow, hC,
      LinearMap.baseChange_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
