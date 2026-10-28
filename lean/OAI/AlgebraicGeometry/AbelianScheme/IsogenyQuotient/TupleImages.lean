import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TuplePoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport

/-! # Tuple Images -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TupleImages.Construction

noncomputable section

/-!
The actual iterated kernel commutes with homomorphic images. In particular,
the torsion inclusion transports the coordinate kernel to the original
abelian scheme without changing its component subgroups.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u

variable {S : Scheme.{u}} {A B C P : Over S} [GrpObj A] [GrpObj B] [GrpObj C]

theorem relativeSubgroupImage_comp (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    SubgroupTransport.Construction.relativeSubgroupImage g (SubgroupTransport.Construction.relativeSubgroupImage f F) = SubgroupTransport.Construction.relativeSubgroupImage (f ≫ g) F := by
  ext X t x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (Category.assoc z f g).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ≫ f, ⟨z, hz, rfl⟩, Category.assoc z f g⟩

variable [IsCommMonObj A] [IsCommMonObj B]

theorem relativeSubgroupImage_tupleKernel (f : A ⟶ B) [IsMonHom f]
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    SubgroupTransport.Construction.relativeSubgroupImage f (Kernel.Tuples.Construction.tupleKernel s F) =
      Kernel.Tuples.Construction.tupleKernel s (fun i => SubgroupTransport.Construction.relativeSubgroupImage f (F i)) := by
  classical
  ext X t x
  rw [TuplePoints.Construction.tupleKernel_points_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := (TuplePoints.Construction.tupleKernel_points_iff s F X t y).mp hy
    refine ⟨(fun i => z i ≫ f), (fun i => ⟨z i, hz i, rfl⟩), ?_⟩
    exact map_prod (IsMonHom.monoidHom f X) _ _
  · rintro ⟨y, hy, rfl⟩
    have hl : ∀ i, ∃ z : X ⟶ A, z ∈ (F i).points X t ∧ z ≫ f = y i := fun i => hy i
    choose z hz hzy using hl
    refine ⟨∏ i, z i, (TuplePoints.Construction.tupleKernel_points_iff s F X t _).mpr ⟨z, hz, rfl⟩, ?_⟩
    change IsMonHom.monoidHom f X (∏ i, z i) = ∏ i, y i
    rw [map_prod]
    exact Finset.prod_congr rfl (fun i _ => hzy i)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TupleImages.Construction
