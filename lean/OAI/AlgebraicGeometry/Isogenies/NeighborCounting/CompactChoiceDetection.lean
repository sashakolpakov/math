import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison
import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection

/-! # Compact Choice Detection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceDetection

noncomputable section

/-! The prescribed compact module type forces the entire chosen block
or the identity subgroup, as functors on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels

variable {S : Scheme} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (q m : ℕ) [NeZero q] (flag : Bool) (p : A ⟶ A) [IsMonHom p]
  [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom] [Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom]

local instance compactModuleAtLevel :
    Module (ZMod (q ^ m)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q m (fun _ => if flag then m else 0)
    (fun _ => by cases flag <;> simp)

def compactBlockFamily : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p) P :=
  if flag then Kernel.Base.fixedKernelFamily (𝟙 _) else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup

def compactBlockFamilyModel : (compactBlockFamily (P := P) q m flag p).Model := by
  cases flag with
  | false => exact AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup_model
  | true => exact Kernel.Base.fixedKernelFamily_model (𝟙 (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p))

variable (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m)
  (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) p P)
  (coordinates : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ S) (_ : Over.mk b ⟶ P),
    Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p) ≃+ (Fin 3 → ZMod (q ^ m)))

include coordinates in
theorem compactChoice_block_eq :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p) F.val.subgroup =
      compactBlockFamily q m flag p := by
  apply AbelianScheme.TorsionQuotient.SubgroupDetection.EtaleSubgroupModels.eq_of_geometric_points
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.supportedTorsionBlock_model (q ^ m) p F.val.subgroup
      (Classical.choice F.val.geometric) F.val.killed F.property)
    (compactBlockFamilyModel q m flag p)
  intro K _ _ b t
  ext z
  let FK : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) p (Over.mk b) :=
    ⟨F.val.baseChange t, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedOn_baseChange F.val.subgroup p F.property t⟩
  have h := Geometric.CompactChoices.geometricCompactChoice_membership q m flag K b p (coordinates K b t) FK (Additive.ofMul z)
  change z ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p ∈ F.val.subgroup.points (Over.mk b) ((𝟙 _) ≫ t) ↔
    if flag then True else z = 1 at h
  rw [Category.id_comp] at h
  cases flag with
  | false => exact h
  | true =>
    constructor
    · intro _
      exact ⟨z, Category.comp_id z⟩
    · intro _
      exact h.mpr trivial

omit [NeZero q] [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom]
  [Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom] in
theorem compactBlockFamily_image :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p) (compactBlockFamily (P := P) q m flag p) =
      if flag then Kernel.Base.fixedKernelFamily (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p) else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  cases flag with
  | false =>
    ext X t z
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y = 1 at hy
      change y ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p = 1
      rw [hy, MonObj.one_comp]
    · intro hz
      change z = 1 at hz
      exact ⟨1, rfl, (MonObj.one_comp (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p)).trans hz.symm⟩
  | true =>
    simpa [compactBlockFamily] using
      (Parameter.ImageComparison.fixedKernelFamily_image (P := P) (𝟙 (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p))
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p))

include coordinates in
theorem compactChoice_eq :
    F.val.subgroup =
      if flag then Kernel.Base.fixedKernelFamily (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p) else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup :=
  (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.supportedTorsionBlock_image (q ^ m) p F.val.subgroup F.val.killed F.property).symm.trans
    ((congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p))
      (compactChoice_block_eq q m flag p F coordinates)).trans
        (compactBlockFamily_image q m flag p))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceDetection
