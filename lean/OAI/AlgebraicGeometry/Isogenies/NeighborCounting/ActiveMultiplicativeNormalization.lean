import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport

/-! # Active Multiplicative Normalization -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeNormalization

noncomputable section

/-! Normalizing the level-one etale labels preserves the actual
multiplicative subgroup and its inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime]
  {G : Grp (Over (Spec (.of k)))} (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q 1 1 2)

theorem chosenActiveMultiplicative_normalization :
    AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q (AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.activeOrdinarySplitting k q e) =
      (AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion := by
  let h : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.etaleOrdinaryBlock k q 1 2 = AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtalePlaneScheme (Spec (.of k)) q :=
    congrArg (fun n => AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.etaleGroupScheme (Spec (.of k))
      (ULift (Multiplicative (Fin 2 → ZMod n)))) (pow_one q)
  change AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion _ _ ≫ ((𝟙 _) ⊗ₘ (eqToIso h).inv) ≫ e.inv =
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion _ _ ≫ e.inv
  rw [← Category.assoc, GroupProductFactorMaps.splitFirstInclusion_tensorHom, Category.id_comp]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeNormalization
