import OAI.RepresentationTheory.Hecke.LieRankZero
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting

/-! # Etale Lie Rank -/

namespace OAI.RepresentationTheory.Hecke.EtaleLieRank.OrdinaryCharacterIntrinsic

noncomputable section

/-! A finite etale coefficient block has zero Lie eigenspace.
Uniqueness of nilpotent lifts is applied to the actual block scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k O : Type} [Field k] [CommRing O] {g : ℕ}
  (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (τ : O →+* k)
  (q : ℕ) [CharP k q] (e : O) (he : τ e = 1)
  [IsFinite (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q e).hom]
  [Etale (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q e).hom]

include q e he

theorem finiteEtaleBlock_eigenpoints_eq
    (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ τ) : x = y := by
  let X := AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q e
  let f := AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ q e
  let bx := LieRankZero.OrdinaryCharacterIntrinsic.lieEigenpointBlockLift A ρ τ q e he x
  let by' := LieRankZero.OrdinaryCharacterIntrinsic.lieEigenpointBlockLift A ρ τ q e he y
  have hx : bx ≫ f = x.val := LieRankZero.OrdinaryCharacterIntrinsic.lieEigenpointBlockLift_inclusion A ρ τ q e he x
  have hy : by' ≫ f = y.val := LieRankZero.OrdinaryCharacterIntrinsic.lieEigenpointBlockLift_inclusion A ρ τ q e he y
  have hk : IsNilpotent (RingHom.ker (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)) := by
    let J := RingHom.ker (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k)
    have hJ : J * J = ⊥ := by
      apply le_antisymm _ bot_le
      apply Ideal.mul_le.mpr
      intro a ha b hb
      change a.fst = 0 at ha
      change b.fst = 0 at hb
      change a * b = 0
      ext <;> simp [ha, hb]
    exact ⟨2, (pow_two J).trans hJ⟩
  have hred : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ bx = AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ by' := by
    apply (cancel_mono f).mp
    exact (Category.assoc _ bx f).trans
      ((congrArg (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ ·) hx).trans
        ((x.property.1.trans y.property.1.symm).trans
          ((congrArg (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin k ≫ ·) hy).symm.trans
            (Category.assoc _ by' f).symm)))
  have hxy := AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InfinitesimalLifting.Construction.finite_etale_nilpotent_hom_ext X.hom
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction k) hk bx.left by'.left (bx.w.trans by'.w.symm)
    (congrArg Over.Hom.left hred)
  apply Subtype.ext
  exact hx.symm.trans ((congrArg (· ≫ f) (Over.OverMorphism.ext hxy)).trans hy)

theorem hasLieRank_eq_zero_of_etaleBlock {r : ℕ}
    (h : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ τ r) : r = 0 :=
  LieRankZero.OrdinaryCharacterIntrinsic.hasLieRank_eq_zero_of_points A ρ τ h (fun x => congrArg Subtype.val
    (finiteEtaleBlock_eigenpoints_eq A ρ τ q e he x (LieRankZero.OrdinaryCharacterIntrinsic.lieIdentityPoint A ρ τ)))

end

end OAI.RepresentationTheory.Hecke.EtaleLieRank.OrdinaryCharacterIntrinsic
