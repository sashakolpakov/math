import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood
import OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport

/-! # Support Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOpen.Constructions

noncomputable section

/-! The genuine reduced product support restricts along the actual
product open immersion to the product of the original restricted supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.Ambient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.OpenNeighborhood.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Diagonal.LocalIsolation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.StalkSupport.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PairSupportKernel.Constructions.Prime OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (j : X ⟶ V.toOver)
  [IsOpenImmersion j.left] [LocallyOfFiniteType X.hom]
  (p q : ℕ) (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport V q)
  (hA : IntersectionGeometry.supportPoint A.val ∈ Set.range j.left) (hB : IntersectionGeometry.supportPoint B.val ∈ Set.range j.left)

local instance : LocallyOfFiniteType V.toOver.hom := inferInstanceAs (LocallyOfFiniteType V.structureMap)

def sourcePairSupport : IrreducibleCloseds (pullback X.hom X.hom : Scheme) :=
  Affine.PairSupportKernel.Constructions.Prime.affinePairSupport X X (Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left A.val hA) (Open.StalkSupport.Constructions.Restriction.restrictedSupport j.left B.val hB)

theorem pair_support_preimage :
    (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) ⁻¹' ((Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val : Set (Diagonal.Ambient.Constructions.productVariety V V).carrier) =
      (sourcePairSupport V X j p q A B hA hB : Set (pullback X.hom X.hom : Scheme)) := by
  change (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) ⁻¹'
    (SupportScheme.Constructions.productIrreducibleSupport V.toOver V.toOver A.val B.val (Diagonal.Ambient.Constructions.productVariety V V).toOver
      (Diagonal.Ambient.Constructions.first V V) (Diagonal.Ambient.Constructions.second V V) (Diagonal.Ambient.Constructions.productLimit V V) : Set (Diagonal.Ambient.Constructions.productVariety V V).toOver.left) = _
  rw [SupportScheme.Constructions.productIrreducibleSupport_coe, sourcePairSupport, Affine.PairSupportKernel.Constructions.Prime.affinePairSupport_coe,
    Open.StalkSupport.Constructions.Restriction.restrictedSupport_coe, Open.StalkSupport.Constructions.Restriction.restrictedSupport_coe]
  have hf : Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j ≫ (Diagonal.Ambient.Constructions.first V V).left = pullback.fst X.hom X.hom ≫ j.left :=
    pullback.lift_fst _ _ _
  have hg : Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j ≫ (Diagonal.Ambient.Constructions.second V V).left = pullback.snd X.hom X.hom ≫ j.left :=
    pullback.lift_snd _ _ _
  ext z
  change ((Diagonal.Ambient.Constructions.first V V).left (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j z) ∈ (A.val : Set V.carrier) ∧
    (Diagonal.Ambient.Constructions.second V V).left (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j z) ∈ (B.val : Set V.carrier)) ↔
      (j.left (pullback.fst X.hom X.hom z) ∈ (A.val : Set V.carrier) ∧
        j.left (pullback.snd X.hom X.hom z) ∈ (B.val : Set V.carrier))
  exact congrArg₂ (fun a b => a ∈ (A.val : Set V.carrier) ∧ b ∈ (B.val : Set V.carrier))
    (congrArg (fun f : pullback X.hom X.hom ⟶ V.carrier => f z) hf)
    (congrArg (fun f : pullback X.hom X.hom ⟶ V.carrier => f z) hg) |>.to_iff

theorem pair_support_genericPoint :
    Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j (IntersectionGeometry.supportPoint (sourcePairSupport V X j p q A B hA hB)) =
      IntersectionGeometry.supportPoint (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val := by
  let C := sourcePairSupport V X j p q A B hA hB
  let D := (Diagonal.LocalIsolation.Constructions.pairedSupport V p q A B).val
  have hc : IntersectionGeometry.supportPoint C ∈ (C : Set (pullback X.hom X.hom : Scheme)) :=
    (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  have hd : Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j (IntersectionGeometry.supportPoint C) ∈ (D : Set (Diagonal.Ambient.Constructions.productVariety V V).carrier) := by
    have h := congrArg (fun S : Set (pullback X.hom X.hom : Scheme) => IntersectionGeometry.supportPoint C ∈ S)
      (pair_support_preimage V X j p q A B hA hB)
    exact h.mpr hc
  have hD := Open.StalkSupport.Constructions.Restriction.generic_mem_range (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) D (IntersectionGeometry.supportPoint C) hd
  have he : Open.StalkSupport.Constructions.Restriction.restrictedSupport (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) D hD = C := by
    apply SetLike.coe_injective
    exact (Open.StalkSupport.Constructions.Restriction.restrictedSupport_coe (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) D hD).trans (pair_support_preimage V X j p q A B hA hB)
  have h := Open.StalkSupport.Constructions.Restriction.restrictedSupport_genericPoint (Diagonal.OpenNeighborhood.Constructions.productOpenMap V X j) D hD
  rw [he] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOpen.Constructions
