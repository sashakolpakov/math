import OAI.AlgebraicGeometry.CycleClass.Geometric.SupportFiniteType
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus

/-! # Singular Codimension -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Ambient codimension of singular points on cycle supports

The generic point of a codimension-p integral support has ambient coheight p.
Every other point is a strict specialization, so its ambient coheight is at
least p+1. Generic smoothness over a perfect field therefore gives this bound
for the singular locus of the actual support structure morphism.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- Every nongeneric point of a codimension-p support has ambient codimension
at least p+1. This uses specialization, not a dimension subtraction formula. -/
theorem CycleClass.Geometric.SingularCodimension.reducedSupport_ambient_coheight_of_ne_generic (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ≠ genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) := by
  have hforward :
      (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) ⤳
        (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x :=
    (genericPoint_specializes x).map (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1).continuous
  have hlt : (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x <
      (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) := by
    rw [lt_iff_le_not_ge]
    refine ⟨Scheme.le_iff_specializes.mpr hforward, ?_⟩
    intro hback
    have hreverse := Scheme.le_iff_specializes.mp hback
    have heq : (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x =
        (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) :=
      (hreverse.antisymm hforward).eq
    exact hx ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1).isClosedEmbedding.injective heq)
  have hbound := Order.coheight_add_one_le hlt
  rw [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_codimension p Z] at hbound
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

variable {K : Type u} [Field K] [PerfectField K]

/-- A singular point of an integral codimension-p support over a perfect field
has ambient codimension at least p+1. -/
theorem CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1 ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1) (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus f) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) := by
  apply CycleClass.Geometric.SingularCodimension.reducedSupport_ambient_coheight_of_ne_generic p Z x
  intro heq
  apply CycleClass.Geometric.SingularLocus.genericPoint_not_mem_singularLocus f
  simpa only [heq] using hx

/-- The singular-codimension bound applies to the actual induced structure
map, whose local finite presentation follows from finite type over the field. -/
theorem CycleClass.Geometric.SingularCodimension.supportStructureMap_singular_ambient_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 f)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) :=
  CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight p Z (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 f) x hx

/-- In particular this controls the singular part of every actual cycle
support in a smooth projective complex presentation. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_singular_ambient_coheight
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) :=
  CycleClass.Geometric.SingularCodimension.supportStructureMap_singular_ambient_coheight p Z P.structureMap x hx

end

end OAI.AlgebraicGeometry
