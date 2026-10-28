import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.Annihilator
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TuplePoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Projector Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorKernel.Construction

noncomputable section

/-!
Identify the subgroup described by projector coordinates with the existing
iterated product of the included block subgroups. Thus the coordinate
isotropy calculation applies to the actual constructed kernel.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u v

variable {S : Scheme.{u}} {T P : Over S} [GrpObj T] [IsCommMonObj T]
  {I : Type v} [Fintype I] (p : I → (T ⟶ T)) [∀ i, IsMonHom (p i)]
  (horth : ∀ i j, i ≠ j → p i ≫ p j = 1)
  (hcomplete : (∏ i, p i) = 𝟙 T)

theorem schemeProjectorPointEquiv_symm_apply (X : Over S)
    (y : ∀ i, X ⟶ BlockGroups.Construction.fixedPointScheme (p i)) :
    (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X).symm y =
      ∏ i, y i ≫ BlockGroups.Construction.fixedPointInclusion (p i) := rfl

theorem decomposed_projector_kernel_eq_tuple
    (H : ∀ i, TorsionQuotient.SubgroupFunctor.RelativeSubgroup (BlockGroups.Construction.fixedPointScheme (p i)) P)
    (s : ℕ) (r : Fin s ≃ I) :
    Product.Annihilator.Construction.decomposedRelativeSubgroup (fun i => BlockGroups.Construction.fixedPointScheme (p i))
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete)
        (Torsion.Decomposition.Construction.schemeProjectorPointEquiv_naturality p horth hcomplete) H =
      Kernel.Tuples.Construction.tupleKernel s (fun j => SubgroupTransport.Construction.relativeSubgroupImage (BlockGroups.Construction.fixedPointInclusion (p (r j))) (H (r j))) := by
  classical
  ext X t x
  rw [Product.Annihilator.Construction.mem_decomposedRelativeSubgroup,
    TuplePoints.Construction.tupleKernel_points_iff_equiv s r
      (fun i => SubgroupTransport.Construction.relativeSubgroupImage (BlockGroups.Construction.fixedPointInclusion (p i)) (H i)) X t x]
  constructor
  · intro hx
    refine ⟨(fun i => Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x i ≫ BlockGroups.Construction.fixedPointInclusion (p i)),
      (fun i => ⟨Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X x i, hx i, rfl⟩), ?_⟩
    exact ((Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X).symm_apply_apply x).symm.trans
      (schemeProjectorPointEquiv_symm_apply p horth hcomplete X _)
  · rintro ⟨y, hy, hxy⟩
    have hl : ∀ i, ∃ z : X ⟶ BlockGroups.Construction.fixedPointScheme (p i),
        z ∈ (H i).points X t ∧ z ≫ BlockGroups.Construction.fixedPointInclusion (p i) = y i := fun i => hy i
    choose z hz hzy using hl
    have hxz : x = (Torsion.Decomposition.Construction.schemeProjectorPointEquiv p horth hcomplete X).symm z := by
      rw [schemeProjectorPointEquiv_symm_apply]
      simpa only [hzy] using hxy
    rw [hxz, MulEquiv.apply_symm_apply]
    exact hz

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProjectorKernel.Construction
