import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke

/-! # Kernel Sum -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelSum

noncomputable section

/-! Evaluating an actual raw kernel is the unweighted sum over its
original inverse-representative coset support. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction

theorem rawKernel_sum {G V : Type*} [Group G] [AddCommMonoid V] [Module ℚ V]
    (U : Subgroup G) (g : G) (T : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.SphericalHecke U) (hT : AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.IsRawDoubleCoset U g T)
    [Fintype (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g)] (v : G ⧸ U → V) :
    (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).sum (fun c a => a • v c) = ∑ c : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g, v c.val := by
  classical
  have hs (c : G ⧸ U) : c ∈ AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g ↔ c ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).support := by
    change c ∈ AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit U g ↔ _
    rw [Finsupp.mem_support_iff, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.raw_kernel_at U hT]
    split_ifs with h <;> simp only [h, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
  let e : AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport U g ≃ {c // c ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).support} :=
    (Equiv.refl (G ⧸ U)).subtypeEquiv hs
  change ∑ c ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).support, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T c • v c = _
  rw [← Finset.sum_attach]
  change (∑ c : {c // c ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).support}, AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T c.val • v c.val) = _
  rw [← e.sum_comp (fun c : {c // c ∈ (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T).support} => AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T c.val • v c.val)]
  apply Finset.sum_congr rfl
  intro c _
  change AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.kernel U T c.val • v c.val = v c.val
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.raw_kernel_at U hT,
    ite_eq_left (show c.val ∈ AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.doubleCosetOrbit U g from c.property), one_smul]

end

end OAI.RepresentationTheory.Theta.Geometric.KernelSum
