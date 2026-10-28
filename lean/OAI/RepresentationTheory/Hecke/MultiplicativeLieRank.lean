import OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents
import OAI.RepresentationTheory.Hecke.LieRankZero

/-! # Multiplicative Lie Rank -/

namespace OAI.RepresentationTheory.Hecke.MultiplicativeLieRank.OrdinaryCharacterIntrinsic

noncomputable section

/-! An embedded split multiplicative block with the actual coefficient
scalar action contributes a nonzero point to that Lie eigenspace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Hecke.OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents

variable {k O M : Type} [Field k] [CommRing O] [CommGroup M] {g : ℕ}
  (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (τ : O →+* k)
  (f : OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (k := k) (M := M) ⟶ A.scheme) [IsMonHom f]
  (index : O → ℕ) (hτ : ∀ a, τ a = (index a : k))
  (hscalar : ∀ (a : O) (T : Over (Spec (.of k))) (x : T ⟶ OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (M := M)),
    (x ≫ f) ≫ ρ.map a = (x ≫ f) ^ index a)

def multiplicativeLiePoint (χ : Additive M →+ k) : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ :=
  ⟨OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ ≫ f, by
    constructor
    · rw [← Category.assoc, OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_reduction, MonObj.one_comp]
    · intro a
      calc
        (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ ≫ f) ≫ ρ.map a = (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ ≫ f) ^ index a := hscalar a _ _
        _ = (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ ^ index a) ≫ f := (MonObj.pow_comp (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ) (index a) f).symm
        _ = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (index a : k) ≫ OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ) ≫ f :=
          congrArg (· ≫ f) (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_nat_scalar χ (index a)).symm
        _ = AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k (τ a) ≫ (OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point χ ≫ f) := by
          rw [hτ a, Category.assoc]⟩

theorem multiplicativeLiePoint_ne_one [Mono f] {χ : Additive M →+ k} (hχ : χ ≠ 0) :
    (multiplicativeLiePoint A ρ τ f index hτ hscalar χ).val ≠ 1 := by
  intro h
  apply OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.point_ne_one hχ
  apply (cancel_mono f).mp
  exact h.trans (MonObj.one_comp f).symm

include f index hτ hscalar in
theorem not_hasLieRank_zero_of_multiplicative [Mono f]
    {χ : Additive M →+ k} (hχ : χ ≠ 0) : ¬ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ 0 := by
  intro h
  exact multiplicativeLiePoint_ne_one A ρ τ f index hτ hscalar hχ
    (LieRankZero.OrdinaryCharacterIntrinsic.hasLieRank_zero_eq_one A ρ τ h (multiplicativeLiePoint A ρ τ f index hτ hscalar χ))

end

end OAI.RepresentationTheory.Hecke.MultiplicativeLieRank.OrdinaryCharacterIntrinsic
