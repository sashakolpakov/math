import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedTorsionKernelFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedAmbientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineInclusion
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedLineAmbientKernel

/-! # Mixed Line Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineFactors.IntrinsicRaw

noncomputable section

/-! The native higher mixed-line kernel has the original independent
mixed inclusion in the abelian source, with no loss of infinitesimal points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedLineAmbientKernel

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (k : Type) [Field k] {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp)
  {n : ℕ} (hn : 1 ≤ n) (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineInclusion

attribute [local irreducible] ActiveChart.nativeActiveChart BlockKernelExhaustion.nativeBlockEmbedding

theorem native_mixed_line_kernel_factor_raw {B : Over (Spec (.of k))} [GrpObj B]
    (f : A.scheme ⟶ B)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ f)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫
          (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e).hom) ≫
            BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ))
    (T : Over (Spec (.of k))) (x : T ⟶ A.scheme)
    (hx : x ^ (q ^ n) = 1) (hp : x ≫ ρ.map (j.projector iota hsplit n τ) = x) :
    type_of% (MixedTorsionKernelFactors.mixed_torsion_kernel_factor k q
    (q ^ n) (ρ.map (j.projector iota hsplit n τ))
    (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e)
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) J e
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ)
    (MixedLineAmbientKernel.chart_embedding_square _ _ _ _ _ _
      (BlockKernelExhaustion.nativeBlockEmbedding_inclusion j iota hsplit A ρ hn τ)
      (ActiveChart.nativeActiveChart_inclusion j iota hsplit k A ρ τ e))
    f hf T x hx hp) :=
  MixedTorsionKernelFactors.mixed_torsion_kernel_factor k q
    (q ^ n) (ρ.map (j.projector iota hsplit n τ))
    (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e)
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) J e
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ)
    (MixedLineAmbientKernel.chart_embedding_square _ _ _ _ _ _
      (BlockKernelExhaustion.nativeBlockEmbedding_inclusion j iota hsplit A ρ hn τ)
      (ActiveChart.nativeActiveChart_inclusion j iota hsplit k A ρ τ e))
    f hf T x hx hp

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineFactors.IntrinsicRaw
