import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport

/-! # XY Active Kernel -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel

noncomputable section

/-! Compute the full higher active-block kernel of X followed by the
independently specified native Y quotient. Only that quotient's original
complete kernel is input; both active restrictions are derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OrdinaryKernelFamilies.IntrinsicOrdinary
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveRestriction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OneStepKernelRecovery OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HigherChosenSupport
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ExhaustiveFrobeniusLine OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PointsFrobeniusMixedLine.CM OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {d N : ℕ} {δ : Fin d → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)

def frobeniusPEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel d δ N (Spec (.of k)) :=
  PEL.pullback (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q Fact.out (Spec (.of k))
    (Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)))

variable (s : ℕ) (labels : (Fin (s + 1) × Bool) ≃ Gal(E/ℚ)) (compact : Fin s → Bool)
variable (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q
  (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PEL.abelian ρ 1 (labels (0, false))).toGrp)
variable (eF : ∀ (m : ℕ) (v : Fin (s + 1)), AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
  (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45ChosenBlock j iota hsplit (frobeniusPEL k PEL)
    (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) (labels (v, false)) m) q m
      (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45MultiplicativeHeights compact v) (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45EtaleHeights compact v))
variable (hdual : ∀ v : Fin (s + 1), PELModuli.CMPoints.DualityPairing.PolarizationDuality (frobeniusPEL k PEL)
  (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ)
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

abbrev targetLineIndex (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :=
  AbelianScheme.FrobeniusKernel.CMPointsLines.Construction.l45FrobeniusLineEquiv j iota hsplit k PEL.abelian ρ (labels (0, false)) e
    (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (eF 1 0)) L

theorem native_XY_active_kernel {C : Over (Spec (.of k))} [GrpObj C]
    (g : (frobeniusPEL k PEL).abelian.scheme ⟶ C) (L : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
    (hkernel : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel g
      (AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45FullYKernelInclusion j iota hsplit (frobeniusPEL k PEL)
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ) s labels compact eF hdual
        (targetLineIndex j iota hsplit k PEL ρ s labels compact e eF L)))
    {n : ℕ} (hn : 1 ≤ n) :
    AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n (labels (0, false)))) ≫
        (AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusIsogeny (q := q) k PEL.abelian).hom ≫ g)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L).hom.hom) ≫
          (ActiveChart.nativeActiveChart j iota hsplit k PEL.abelian ρ (labels (0, false)) e).hom) ≫
            BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit PEL.abelian ρ hn (labels (0, false))) := by
  let τ := labels (0, false)
  let σ := AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k PEL.abelian ρ
  let ep := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q (eF 1 0)
  let L' := targetLineIndex j iota hsplit k PEL ρ s labels compact e eF L
  let H0 := AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.l45ActiveYChosenSubgroup j iota hsplit (frobeniusPEL k PEL) σ τ (eF 1 0) L'
  let P0 := AbelianScheme.FrobeniusKernel.CMPointsYZQuotients.Construction.l45OrdinaryCoordinatesFamily j iota hsplit (frobeniusPEL k PEL) σ s labels compact eF 1
  let ein := (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom ≫
    AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (frobeniusPEL k PEL).abelian σ 1 τ
  let h : H0.group.X ⟶ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X :=
    (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q L').hom.hom
  have : IsClosedImmersion ein.left := by
    have := AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane_closed k q ep
    have : IsClosedImmersion
        (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (frobeniusPEL k PEL).abelian σ 1 τ).left :=
      PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed (frobeniusPEL k PEL).abelian σ _ _
    change IsClosedImmersion ((AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom.left ≫
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (frobeniusPEL k PEL).abelian σ 1 τ).left)
    infer_instance
  have : Mono ein := Over.mono_of_mono_left _
  have : IsClosedImmersion h.left := AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding_closed (Spec (.of k)) q L'
  have : Mono h := Over.mono_of_mono_left _
  have hsquare : h ≫ ein = H0.inclusion.hom.hom ≫
      AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (frobeniusPEL k PEL).abelian σ 1 τ :=
    (Category.assoc h (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep).hom.hom
      (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit (frobeniusPEL k PEL).abelian σ 1 τ)).symm
  have hsupport := HigherChosenSupport.original_block_inclusion_supported_higher j iota hsplit
    (frobeniusPEL k PEL).abelian σ (Nat.le_refl 1) τ (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtalePlane k q ep)
  have hr := ActiveRestriction.native_restricted_active_kernel j iota hsplit (frobeniusPEL k PEL) σ 1 s labels compact
    (eF 1) H0 P0 hdual g hkernel ein h hsquare (Nat.le_refl 1) hsupport
  apply ExhaustiveFrobeniusLine.exhaustive_frobenius_line j iota hsplit k PEL.abelian ρ τ e ep g L hn hr
  intro T a ha hk
  exact OneStepKernelRecovery.native_one_step_active_factor j iota hsplit (frobeniusPEL k PEL) σ 1 s labels compact
    (eF 1) H0 P0 hdual g hkernel hn T a ha hk

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.XYActiveKernel
