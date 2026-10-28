import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates

/-! # Subgroup Iso Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubgroupIsoTransport

noncomputable section

/-! Transport actual subgroup functors through source isomorphisms,
retaining products and the original commuting inclusion square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts OAI.AlgebraicGeometry.Isogenies.NeighborCounting.GroupProductCoordinates

universe u

variable {S : Scheme.{u}} {A B P : Over S} [GrpObj A] [GrpObj B]
  (e : A ≅ B) [IsMonHom e.hom]

theorem subgroupImage_iso_eq_pullback (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage e.hom F = AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.inv F := by
  ext T t y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ F.points T t at hx
    change (x ≫ e.hom) ≫ e.inv ∈ F.points T t
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hx
  · intro hy
    refine ⟨y ≫ e.inv, hy, ?_⟩
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => y ≫ z) e.inv_hom_id).trans (Category.comp_id y))

theorem subgroupPullback_composite {C : Over S} [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g]
    (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup C P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback f (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback g F) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback (f ≫ g) F := by
  ext T t x
  change (x ≫ f) ≫ g ∈ F.points T t ↔ x ≫ (f ≫ g) ∈ F.points T t
  rw [Category.assoc]

section Commutative

variable [IsCommMonObj A] [IsCommMonObj B]

theorem subgroupPullback_iso_trivial :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup (P := P)) = AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  ext T t x
  change x ≫ e.hom = 1 ↔ x = 1
  exact (GroupProductCoordinates.groupPointIso (T := T) e).map_eq_one_iff

theorem subgroupPullback_iso_product (F G : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct F G) =
      AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom F) (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom G) := by
  ext T t x
  exact SetLike.ext_iff.mp
    (Parameter.KernelProducts.subgroupProduct_comap_equiv (GroupProductCoordinates.groupPointIso (T := T) e) (F.points T t) (G.points T t)) x

theorem subgroupPullback_iso_tuple (s : ℕ) (F : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup B P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s F) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun i => AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (F i)) := by
  induction s with
  | zero => exact subgroupPullback_iso_trivial e
  | succ s ih =>
    change AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom
      (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F 0) (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun i => F i.succ))) = _
    rw [subgroupPullback_iso_product, ih]
    rfl

end Commutative

theorem subgroupPullback_image_square {G H : Over S} [GrpObj G] [GrpObj H]
    (d : G ≅ H) [IsMonHom d.hom] (i : G ⟶ A) (j : H ⟶ B) [IsMonHom i] [IsMonHom j]
    (square : d.hom ≫ j = i ≫ e.hom) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H P) :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback e.hom (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage j F) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage i (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback d.hom F) := by
  ext T t y
  constructor
  · rintro ⟨x, hx, hxy⟩
    change x ∈ F.points T t at hx
    refine ⟨x ≫ d.inv, ?_, ?_⟩
    · change (x ≫ d.inv) ≫ d.hom ∈ F.points T t
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hx
    · apply (cancel_mono e.hom).mp
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => (x ≫ d.inv) ≫ z) square.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun z => z ≫ j)
              ((Category.assoc _ _ _).trans
                ((congrArg (fun z => x ≫ z) d.inv_hom_id).trans (Category.comp_id x)))).trans hxy)))
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x ≫ d.hom, hx, ?_⟩
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => x ≫ z) square).trans (Category.assoc _ _ _).symm)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubgroupIsoTransport
