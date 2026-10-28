import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport

/-! # Compact Chosen Families -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChosenFamilies

noncomputable section

/-! The original ordinary compact chosen subgroup gives exactly the
whole or identity family at its literal torsion level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport.Family

variable {k : Type} [Field k] {q : ℕ} [Fact q.Prime] {n : ℕ}
variable {G : Grp (Over (Spec (.of k)))} {A X : Over (Spec (.of k))}
variable [GrpObj A] [IsCommMonObj A]
variable (gin : G.X ⟶ A) [IsMonHom gin]

omit [IsCommMonObj A] in
theorem pure_multiplicative_family {d : ℕ} (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n d 0) :
    Kernel.Base.fixedKernelFamily (P := X) ((AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion.hom.hom ≫ gin) =
      Kernel.Base.fixedKernelFamily (P := X) gin :=
  Kernel.FamilyTransport.Family.fixed_iso _ _ (@asIso _ _ _ _ (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom
    (AbelianScheme.FrobeniusKernel.CompactKernels.Construction.ordinaryPureMultiplicative_inclusion_isIso k q n e)) rfl

theorem pure_etale_family {r : ℕ} (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n 0 r) :
    Kernel.Base.fixedKernelFamily (P := X) ((AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion.hom.hom ≫ gin) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  ext T t a
  change (∃ b, b ≫ ((AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom ≫ gin) = a) ↔ a = 1
  constructor
  · rintro ⟨b, rfl⟩
    rw [← Category.assoc, AbelianScheme.FrobeniusKernel.CompactKernels.Construction.ordinaryPureEtale_inclusion_zero, MonObj.one_comp]
  · rintro rfl
    exact ⟨1, MonObj.one_comp _⟩

theorem compact_chosen_family (compact : Bool)
    (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k G q n (if compact then 3 else 0) (if compact then 0 else 3)) :
    Kernel.Base.fixedKernelFamily (P := X) ((AbelianScheme.FrobeniusKernel.FiniteCartierSubgroupTransport.Construction.multiplicativeChosenSubgroup e).inclusion.hom.hom ≫ gin) =
      if compact then Kernel.Base.fixedKernelFamily (P := X) gin else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  cases compact
  · exact pure_etale_family gin e
  · exact pure_multiplicative_family gin e

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChosenFamilies
