import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedAmbientKernel
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors

/-! # Mixed Torsion Kernel Factors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedTorsionKernelFactors

noncomputable section

/-! Transport of a mixed kernel from a torsion block to its ambient group. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedAmbientKernel.Raw OAI.AlgebraicGeometry.Isogenies.NeighborCounting.AmbientKernelFactors

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime]
  {A B C : Over (Spec (.of k))} [GrpObj A] [IsCommMonObj A] [GrpObj B]
  (n : ℕ) (p : A ⟶ A) [IsMonHom p]
  (c : (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q).X ≅ C)
  (b : C ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) [Mono b] (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q)
  {G : Grp (Over (Spec (.of k)))} (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q G)
  (l : G.X ⟶ A)

theorem mixed_torsion_kernel_factor
    (hc : c.hom ≫ b ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p = e.inv.hom.hom ≫ l)
    (f : A ⟶ B)
    (hf : AbelianScheme.FrobeniusKernel.Prescribed.Construction.PrescribedKernel (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p ≫ f)
      (((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ₘ
        (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J).hom.hom) ≫ c.hom) ≫ b))
    (T : Over (Spec (.of k))) (x : T ⟶ A) (hx : x ^ n = 1) (hp : x ≫ p = x) :
    x ≫ f = 1 ↔ ∃ h : T ⟶
      (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1).X ⊗ (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J).X,
      h ≫ (ActiveMixedLineTransport.chosenActiveMixedLine k q e J).hom.hom ≫ l = x := by
  have h := AmbientKernelFactors.ambient_kernel_factor_iff f (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p) _ hf x
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift n p x hx hp) (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion n p x hx hp)
  exact h.trans (MixedAmbientKernel.Raw.raw_mixed_factor_iff k q c b J e (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p) l hc T x)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.MixedTorsionKernelFactors
