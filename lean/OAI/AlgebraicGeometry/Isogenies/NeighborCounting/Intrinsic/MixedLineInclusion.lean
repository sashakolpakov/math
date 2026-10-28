import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ActiveChart
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedLineAmbientKernel

/-! # Mixed Line Inclusion -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineInclusion

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

def nativeMixedLineInclusion :
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X ⟶
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ)) :=
  MixedLineAmbientKernel.mixedLineKernelInclusion k q (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e)
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) J

instance nativeMixedLineInclusion_mono : Mono (nativeMixedLineInclusion j iota hsplit k A ρ τ e hn J) :=
  MixedLineAmbientKernel.mixedLineKernelInclusion_mono k q (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e)
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) J

theorem nativeMixedLineInclusion_ambient :
    nativeMixedLineInclusion j iota hsplit k A ρ τ e hn J ≫
      AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) =
    (ActiveMixedLineTransport.chosenActiveMixedLine k q e J).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ :=
  MixedLineAmbientKernel.mixedLineKernelInclusion_ambient k q (ActiveChart.nativeActiveChart j iota hsplit k A ρ τ e)
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) J e
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)))
    (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ)
    (MixedLineAmbientKernel.chart_embedding_square _ _ _ _ _ _
      (BlockKernelExhaustion.nativeBlockEmbedding_inclusion j iota hsplit A ρ hn τ)
      (ActiveChart.nativeActiveChart_inclusion j iota hsplit k A ρ τ e))

theorem native_mixed_line_kernel_factor {B : Over (Spec (.of k))} [GrpObj B]
    (f : A.scheme ⟶ B)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ f)
      (nativeMixedLineInclusion j iota hsplit k A ρ τ e hn J))
    (T : Over (Spec (.of k))) (x : T ⟶ A.scheme)
    (hx : x ^ (q ^ n) = 1) (hp : x ≫ ρ.map (j.projector iota hsplit n τ) = x) :
    x ≫ f = 1 ↔
      ∃ h : T ⟶ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X,
        h ≫ (ActiveMixedLineTransport.chosenActiveMixedLine k q e J).hom.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ = x := by
  have h := AmbientKernelFactors.native_block_kernel_factor j iota hsplit A ρ n τ f
    (nativeMixedLineInclusion j iota hsplit k A ρ τ e hn J) hf T x hx hp
  have he := Iff.of_eq (congrArg (fun u => ∃ h : T ⟶
    (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X, h ≫ u = x)
    (nativeMixedLineInclusion_ambient j iota hsplit k A ρ τ e hn J))
  exact h.trans he

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.MixedLineInclusion
