import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation
import OAI.AlgebraicGeometry.CycleClass.Geometric.ProjectiveComponentCycles

/-! # Component Serre -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions

/-! The actual finite Serre pair cycle restricts to the same native
cycle on its integral component and vanishes on other components. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentIntersection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProjectiveSupportIsolation.Constructions.Intersection OAI.AlgebraicGeometry.CycleClass.Thom.Supported.Map.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

theorem generic_mem_image_component (C D : irreducibleComponents X.carrier)
    (A : IrreducibleCloseds (X.componentVariety C).carrier)
    (Z : IrreducibleCloseds (X.componentVariety D).carrier)
    (hx : IntersectionGeometry.supportPoint (X.componentSupportImage D Z) ∈ (X.componentSupportImage C A : Set X.carrier)) : C = D := by
  have hs := (Intersection.Supports.supportPoint_mem_iff_subset (⟨X.componentSupportImage C A, (X.componentSupportImage C A).isClosed⟩ : Closeds X.carrier)
    (X.componentSupportImage D Z)).mp hx
  have h := X.supportComponent_eq_of_subset (X.componentSupportImage D Z) C
    (fun _ hz => X.componentSupportImage_subset C A (hs hz))
  rw [X.supportComponent_image] at h
  exact h.symm

theorem multiplicity_other_component_left (C D : irreducibleComponents X.carrier)
    (A : IrreducibleCloseds (X.componentVariety C).carrier) (B : IrreducibleCloseds X.carrier)
    (Z : IrreducibleCloseds (X.componentVariety D).carrier) (hCD : C ≠ D) :
    IntersectionGeometry.intersectionMultiplicity X (X.componentSupportImage C A) B (X.componentSupportImage D Z) = 0 :=
  dite_eq_right (fun h => hCD (generic_mem_image_component X C D A Z h.1))

theorem multiplicity_other_component_right (C D : irreducibleComponents X.carrier)
    (A : IrreducibleCloseds X.carrier) (B : IrreducibleCloseds (X.componentVariety C).carrier)
    (Z : IrreducibleCloseds (X.componentVariety D).carrier) (hCD : C ≠ D) :
    IntersectionGeometry.intersectionMultiplicity X A (X.componentSupportImage C B) (X.componentSupportImage D Z) = 0 :=
  dite_eq_right (fun h => hCD (generic_mem_image_component X C D B Z h.2))

variable (C : irreducibleComponents X.carrier) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (B : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) q)

local notation "AX" => Equiv.symm (X.componentDimensionSupportEquiv p) (Sigma.mk C A)
local notation "BX" => Equiv.symm (X.componentDimensionSupportEquiv q) (Sigma.mk C B)

theorem component_pair_proper (h : Proper.Intersection.pairMeetsProperly X p q AX BX) :
    ∀ Z : IrreducibleCloseds (X.componentVariety C).carrier,
      (Z : Set (X.componentVariety C).carrier) ⊆ Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed (X.componentVariety C) p q A B →
        p + q ≤ Geometric.DimensionCycles.dimensionCodimension (X.componentVariety C) Z := by
  intro Z hZ
  have hh := h (X.componentSupportImage C Z) (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, (hZ hz).1, rfl⟩, ⟨z, (hZ hz).2, rfl⟩⟩)
  rwa [X.supportCodimension_componentSupportImage] at hh

theorem pairCycle_restrict_same (h : Proper.Intersection.pairMeetsProperly X p q AX BX) :
    X.componentDimensionCycleEquiv (p + q) (Proper.Intersection.pairCycle X p q AX BX) C =
      Supported.Map.Constructions.forgetCycle (X.componentVariety C) (Supported.ProjectiveSupportIsolation.Constructions.Intersection.intersectionClosed (X.componentVariety C) p q A B) (p + q)
        (Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle (X.componentVariety C) p q A B (component_pair_proper X C p q A B h)) := by
  ext Z
  rw [X.componentDimensionCycleEquiv_apply, Proper.Intersection.pairCycle_apply X p q AX BX h,
    Supported.ProjectiveSupportIsolation.Constructions.Intersection.supportedPairCycle_forget_coefficient]
  exact (ComponentIntersection.Constructions.multiplicity_image X C A.val B.val Z.val).symm

theorem pairCycle_restrict_other (h : Proper.Intersection.pairMeetsProperly X p q AX BX)
    (D : irreducibleComponents X.carrier) (hCD : C ≠ D) :
    X.componentDimensionCycleEquiv (p + q) (Proper.Intersection.pairCycle X p q AX BX) D = 0 := by
  ext Z
  rw [X.componentDimensionCycleEquiv_apply, Proper.Intersection.pairCycle_apply X p q AX BX h, Finsupp.zero_apply]
  exact multiplicity_other_component_left X C D A.val (X.componentSupportImage C B.val) Z.val hCD

end AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions.Mixed

/-! Actual supports in distinct integral components have zero native
Serre intersection cycle on the original presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Proper.Intersection

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pairCycle_mixed_zero (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C D : irreducibleComponents X.carrier) (p q : ℕ)
    (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (B : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety D) q)
    (hCD : C ≠ D)
    (hp : Proper.Intersection.pairMeetsProperly X p q ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩)
      ((X.componentDimensionSupportEquiv q).symm ⟨D, B⟩)) :
    Proper.Intersection.pairCycle X p q ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩)
      ((X.componentDimensionSupportEquiv q).symm ⟨D, B⟩) = 0 := by
  ext T
  obtain ⟨⟨E, Z⟩, rfl⟩ := (X.componentDimensionSupportEquiv (p + q)).symm.surjective T
  rw [Proper.Intersection.pairCycle_apply X p q _ _ hp, Finsupp.zero_apply]
  by_cases he : C = E
  · subst E
    exact multiplicity_other_component_right X D C (X.componentSupportImage C A.val) B.val Z.val (Ne.symm hCD)
  · exact multiplicity_other_component_left X C E A.val (X.componentSupportImage D B.val) Z.val he

end AlgebraicGeometry.CycleClass.Thom.ComponentSerre.Constructions.Mixed

end

end OAI
