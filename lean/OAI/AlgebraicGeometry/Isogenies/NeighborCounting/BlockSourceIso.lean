import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OppositeKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupMaps

/-! # Block Source Iso -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso

noncomputable section

/-! Equivariant source isomorphisms carry the actual fixed torsion
blocks to one another, with their original ambient inclusions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {A B : Over S} [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (n : ℕ)
  (p : A ⟶ A) (r : B ⟶ B) [IsMonHom p] [IsMonHom r]

def blockSourceMap (f : A ⟶ B) [IsMonHom f] (hf : p ≫ f = f ≫ r) :
    AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift n r (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p ≫ f)
    (by rw [← MonObj.pow_comp, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_killed, MonObj.one_comp])
    (by rw [Category.assoc, ← hf, ← Category.assoc, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion_supported])

theorem blockSourceMap_inclusion (f : A ⟶ B) [IsMonHom f] (hf : p ≫ f = f ≫ r) :
    blockSourceMap n p r f hf ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r = AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p ≫ f :=
  AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _

instance blockSourceMap_isMonHom (f : A ⟶ B) [IsMonHom f] (hf : p ≫ f = f ≫ r) :
    IsMonHom (blockSourceMap n p r f hf) := by
  apply AbelianScheme.IsogenyQuotient.GroupMaps.Construction.isMonHom_of_pointwise
  · intro T
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r)).mp
    simp only [Category.assoc, blockSourceMap_inclusion, MonObj.one_comp]
  · intro T a b
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r)).mp
    simp only [Category.assoc, blockSourceMap_inclusion, MonObj.mul_comp]

variable (e : A ≅ B) [IsMonHom e.hom] (he : p ≫ e.hom = e.hom ≫ r)

include he in
omit [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  [IsMonHom p] [IsMonHom r] [IsMonHom e.hom] in
theorem sourceIso_inverse_comm : r ≫ e.inv = e.inv ≫ p := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← he, Category.assoc, e.hom_inv_id, Category.comp_id,
    e.hom_inv_id_assoc]

def blockSourceIso : AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p ≅ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r where
  hom := blockSourceMap n p r e.hom he
  inv := blockSourceMap n r p e.inv (sourceIso_inverse_comm p r e he)
  hom_inv_id := by
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p)).mp
    rw [Category.assoc, blockSourceMap_inclusion, ← Category.assoc, blockSourceMap_inclusion,
      Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r)).mp
    rw [Category.assoc, blockSourceMap_inclusion, ← Category.assoc, blockSourceMap_inclusion,
      Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

instance blockSourceIso_isMonHom : IsMonHom (blockSourceIso n p r e he).hom :=
  blockSourceMap_isMonHom n p r e.hom he

def blockSourceGroupIso : Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n p) ≅ Grp.mk (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n r) :=
  Grp.mkIso' (blockSourceIso n p r e he)

theorem blockSourceIso_inclusion :
    (blockSourceIso n p r e he).hom ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n r = AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n p ≫ e.hom :=
  blockSourceMap_inclusion n p r e.hom he

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.BlockSourceIso
