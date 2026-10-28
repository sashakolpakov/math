import OAI.AlgebraicGeometry.CycleClass.Geometric.GenericPoint
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Singular Locus -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus

noncomputable section

/-!
# Algebraic singular loci of cycle supports

This file uses the actual smooth locus of a morphism of schemes. Over a perfect
field, a reduced finite-presentation scheme is generically smooth. Consequently
its nonsmooth locus is closed with empty interior; in the integral case all its
points have positive intrinsic codimension.

These are algebraic inputs to a future fundamental-class construction. They do
not identify a complex analytic singular locus, assert a triangulation, or
postulate a fundamental class.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The nonsmooth locus, defined from the formal smoothness of actual stalk maps. -/
def singularLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : Set X :=
  (f.smoothLocus : Set X)ᶜ

@[simp]
theorem mem_singularLocus_iff (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    x ∈ singularLocus f ↔ ¬ (f.stalkMap x).hom.FormallySmooth := Iff.rfl

theorem isClosed_singularLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    IsClosed (singularLocus f) := f.smoothLocus.isOpen.isClosed_compl

@[simp]
theorem singularLocus_eq_empty_of_smooth (f : X ⟶ Y) [Smooth f] :
    singularLocus f = ∅ := by
  simp only [singularLocus, f.smoothLocus_eq_top, Opens.coe_top, Set.compl_univ]

variable {K : Type u} [Field K] [PerfectField K]

/-- Generic smoothness makes the singular locus nowhere dense as a closed set. -/
theorem interior_singularLocus_eq_empty [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    interior (singularLocus f) = ∅ :=
  f.dense_smoothLocus_of_perfectField.interior_compl

theorem interior_closure_singularLocus_eq_empty [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    interior (closure (singularLocus f)) = ∅ := by
  rw [(isClosed_singularLocus f).closure_eq, interior_singularLocus_eq_empty]

theorem genericPoint_not_mem_singularLocus [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    genericPoint X ∉ singularLocus f := by
  intro hsing
  change ¬ (f.stalkMap (genericPoint X)).hom.FormallySmooth at hsing
  have hsm := f.genericPoint_mem_smoothLocus_of_perfectField
  change (f.stalkMap (genericPoint X)).hom.FormallySmooth at hsm
  exact hsing hsm

/-- A nonsmooth point on an integral finite-presentation scheme over a perfect
field has positive codimension in that scheme. -/
theorem coheight_pos_of_mem_singularLocus [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : X) (hx : x ∈ singularLocus f) : 0 < Order.coheight x := by
  apply Order.coheight_pos.mpr
  intro hmax
  have hgen : genericPoint X ⤳ x := genericPoint_specializes x
  have hback : x ⤳ genericPoint X := hmax hgen
  have heq : x = genericPoint X := (hback.antisymm hgen).eq
  apply genericPoint_not_mem_singularLocus f
  simpa only [heq] using hx

/-- The reduced integral closed subscheme attached to an irreducible cycle
support has a dense smooth locus whenever its structure morphism is of finite
presentation locally. -/
theorem reducedSupport_dense_smoothLocus (Z : IrreducibleCloseds X)
    (f : GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    Dense (f.smoothLocus : Set (GenericPoint.reducedSupportScheme Z)) :=
  f.dense_smoothLocus_of_perfectField

/-- In particular the singular part of an actual cycle support has positive
intrinsic codimension at every point. -/
theorem reducedSupport_singular_coheight_pos (Z : IrreducibleCloseds X)
    (f : GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : GenericPoint.reducedSupportScheme Z) (hx : x ∈ singularLocus f) :
    0 < Order.coheight x :=
  coheight_pos_of_mem_singularLocus f x hx

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus
