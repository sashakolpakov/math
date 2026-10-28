import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps

/-! # Active Mixed Line Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport

noncomputable section

/-! The product of the intrinsic multiplicative factor and each etale
line transports through any actual isomorphism of ordinary active blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMultiplicativeTransport OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductFactorMaps

variable (k : Type) [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
  {B B' : Grp (Over (Spec (.of k)))}
  (e : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B) (e' : AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.ActiveOrdinarySplitting k q B')

def chosenActiveMixedLine (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J ⟶ B :=
  ((𝟙 (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1)) ⊗ₘ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineEmbedding (Spec (.of k)) q J) ≫ e.inv

omit [CharP k q] in
theorem chosenActiveMixedLine_first (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1)
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J) ≫ chosenActiveMixedLine k q e J =
        AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveMultiplicative k q e := by
  unfold chosenActiveMixedLine
  rw [← Category.assoc, GroupProductFactorMaps.splitFirstInclusion_tensorHom, Category.id_comp]
  rfl

omit [CharP k q] in
theorem chosenActiveMixedLine_second (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1)
      (AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J) ≫ chosenActiveMixedLine k q e J =
        AbelianScheme.FrobeniusKernel.ChosenOrdinaryKernels.Construction.chosenActiveEtaleLine k q e J := by
  unfold chosenActiveMixedLine
  rw [← Category.assoc, GroupProductFactorMaps.splitSecondInclusion_tensorHom, Category.assoc]
  rfl

def chosenActiveMixedLineIso (a : B ≅ B') (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q J ≅
      AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.multiplicativeOrdinaryBlock k q 1 1 ⊗ AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.activeEtaleLineScheme (Spec (.of k)) q
        (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineEquiv k q e e' a J) :=
  tensorIso (ActiveMultiplicativeTransport.activeMultiplicativeIso k q e e' a) (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso k q e e' a J)

theorem chosenActiveMixedLineIso_inclusion (a : B ≅ B') (J : AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction.ActiveEtaleLine q) :
    (chosenActiveMixedLineIso k q e e' a J).hom ≫
      chosenActiveMixedLine k q e' (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineEquiv k q e e' a J) =
        chosenActiveMixedLine k q e J ≫ a.hom := by
  apply GroupProductFactorMaps.group_product_hom_ext
  · change AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitFirstInclusion _ _ ≫
      (((ActiveMultiplicativeTransport.activeMultiplicativeIso k q e e' a).hom ⊗ₘ (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso k q e e' a J).hom) ≫
        chosenActiveMixedLine k q e' (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineEquiv k q e e' a J)) = _
    rw [← Category.assoc, GroupProductFactorMaps.splitFirstInclusion_tensorHom, Category.assoc,
      chosenActiveMixedLine_first, ActiveMultiplicativeTransport.activeMultiplicativeIso_inclusion,
      ← chosenActiveMixedLine_first k q e J, Category.assoc]
  · change AbelianScheme.FrobeniusKernel.AnnihilatorSheaf.Construction.splitSecondInclusion _ _ ≫
      (((ActiveMultiplicativeTransport.activeMultiplicativeIso k q e e' a).hom ⊗ₘ (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso k q e e' a J).hom) ≫
        chosenActiveMixedLine k q e' (AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineEquiv k q e e' a J)) = _
    rw [← Category.assoc, GroupProductFactorMaps.splitSecondInclusion_tensorHom, Category.assoc,
      chosenActiveMixedLine_second, AbelianScheme.FrobeniusKernel.ActiveEtaleTransport.Construction.chosenActiveLineIso_inclusion,
      ← chosenActiveMixedLine_second k q e J, Category.assoc]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveMixedLineTransport
