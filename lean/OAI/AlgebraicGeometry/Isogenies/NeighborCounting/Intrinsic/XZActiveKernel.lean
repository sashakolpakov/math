import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine

/-! # XZ Active Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XZActiveKernel

noncomputable section

/-! Compute the active kernel of X followed by the independently
defined native Z quotient. Z's chosen group is still the q-torsion
plane inside level two; the mixed kernel is the source q-block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine.Plane OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (compact : Fin s → Bool)
variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 (labels (0, false))).toGrp)
variable (eF : ∀ (m : ℕ) (v : Fin (s + 1)), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (XYActiveKernel.frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v, false)) m) q m
      (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality (XYActiveKernel.frobeniusPEL k PEL)
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ)
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

include e in
theorem native_XZ_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : (XYActiveKernel.frobeniusPEL k PEL).abelian.scheme ⟶ C)
    (hkernel : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel g
      (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45FullZKernelInclusion j iota hsplit (XYActiveKernel.frobeniusPEL k PEL)
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) s labels compact eF hdual))
    {n : ℕ} (hn : 2 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (0, false)))) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g)
      (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PEL.abelian ρ
        (Nat.le_trans (show 1 ≤ 2 by decide) hn) (labels (0, false))) := by
  let τ := labels (0, false)
  let σ := AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ
  let ep := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (eF 1 0)
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveZChosenSubgroup j iota hsplit (XYActiveKernel.frobeniusPEL k PEL) σ τ (eF 1 0)
  let P0 := AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45OrdinaryCoordinatesFamily j iota hsplit (XYActiveKernel.frobeniusPEL k PEL) σ s labels compact eF 2
  let i := H0.inclusion.hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (XYActiveKernel.frobeniusPEL k PEL).abelian σ 2 τ
  have hi : i = PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PEL.abelian ρ τ ep :=
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ActivePlaneAtLevelTwo_inclusion j iota hsplit (XYActiveKernel.frobeniusPEL k PEL) σ τ (eF 1 0)
  have hz := ActiveRestriction.native_one_step_chosen_killed j iota hsplit (XYActiveKernel.frobeniusPEL k PEL) σ 2 s labels compact
    (eF 2) H0 P0 hdual g hkernel H0.group.X (𝟙 _)
  have hg : i ≫ g = 1 := (congrArg (fun z => z ≫ g) (Category.id_comp i)).symm.trans hz
  have hplane : PointsFrobeniusMixedLine.CM.targetPlane j iota hsplit k PEL.abelian ρ τ ep ≫ g = 1 :=
    (congrArg (fun z => z ≫ g) hi.symm).trans hg
  apply ExhaustiveFrobeniusLine.Plane.exhaustive_frobenius_plane j iota hsplit k PEL.abelian ρ τ e ep g
    (Nat.le_trans (show 1 ≤ 2 by decide) hn) hplane
  intro T a ha hk
  obtain ⟨b, hb⟩ := OneStepKernelRecovery.native_one_step_active_factor j iota hsplit (XYActiveKernel.frobeniusPEL k PEL) σ 2 s labels compact
    (eF 2) H0 P0 hdual g hkernel hn T a ha hk
  exact ⟨b, (congrArg (fun z => b ≫ z) hi).symm.trans hb⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XZActiveKernel
