import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.CMPointsBlockComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Block Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockFactors

noncomputable section

/-! The native full q-block kernel has the original CMPoints chosen-block
factorization criterion in the abelian source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockKernelExhaustion OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FactorSquares

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} {d : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  {n : ℕ} (hn : 1 ≤ n) (τ : Gal(E/ℚ))

theorem native_full_block_kernel_factor {B : Over S} [GrpObj B]
    (f : A.scheme ⟶ B)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) ≫ f)
      (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ))
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ (q ^ n) = 1)
    (hp : x ≫ ρ.map (j.projector iota hsplit n τ) = x) :
    x ≫ f = 1 ↔ ∃ h : T ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp.X,
      h ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ = x := by
  have h := AmbientKernelFactors.native_block_kernel_factor j iota hsplit A ρ n τ f
    (BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ) hf T x hx hp
  let e := AbelianScheme.IsogenyQuotient.CM.PointsProjectorSum.Construction.l45NativeBlockIso j iota hsplit A ρ 1 τ
  have he : e.hom ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ =
      BlockKernelExhaustion.nativeBlockEmbedding j iota hsplit A ρ hn τ ≫
        AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ n) (ρ.map (j.projector iota hsplit n τ)) :=
    (CMPointsBlockComparison.l45NativeBlockIso_inclusion j iota hsplit A ρ 1 τ).trans
      (BlockKernelExhaustion.nativeBlockEmbedding_inclusion j iota hsplit A ρ hn τ).symm
  exact h.trans (Kernel.FactorSquares.factor_iff_of_carrier_iso e _ _ he x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockFactors
