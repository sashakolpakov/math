import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Residual
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.ImageBounds

/-! # Residual Intersection -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualIntersection

noncomputable section

section

/-! The off-diagonal incidence image contains every residual
intersection point outside the original support and obeys its dimension bound. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace IncidenceImage

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)

abbrev secondMap : Support.Pair.space X W Z ⟶ X.carrier := (Support.Pair.second X W Z).left

instance second_proper : IsProper (secondMap X W Z) :=
  inferInstanceAs (IsProper (pullback.snd (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ X.structureMap)
    (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ X.structureMap) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z))

theorem second_over : secondMap X W Z ≫ X.structureMap = Support.Pair.base X W Z := (Support.Pair.second X W Z).w

variable {m : ℕ} (π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m))

def removed : Closeds (Support.Pair.space X W Z) := ClosedDifferenceDimension.away
  (Generic.Finite.Projection.coincidence X W Z π) (Support.PairIncidenceStep.diagonal X W Z)

def image : Closeds X.carrier := Proper.ImageBounds.image X (secondMap X W Z) (removed X W Z π)

theorem bound (d : ℕ)
    (hI : ∀ C : IrreducibleCloseds (Support.Pair.space X W Z), (C : Set (Support.Pair.space X W Z)) ⊆ Generic.Finite.Projection.coincidence X W Z π →
      ¬ (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X W Z) + m ≤ d) :
    ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ image X W Z π →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + m ≤ d := by
  apply Proper.ImageBounds.bound X (secondMap X W Z) (removed X W Z π) m d
  rw [second_over]
  exact ClosedDifferenceDimension.bound (Generic.Finite.Projection.coincidence X W Z π)
    (Support.PairIncidenceStep.diagonal X W Z) (Support.Pair.base X W Z) m d hI

variable [IsFinite π.left]

theorem mem_image (y : X.carrier) (hy : IsClosed {y}) (hyZ : y ∈ Z) (hyW : y ∉ W)
    (hyπ : π.left y ∈ π.left '' (W : Set X.carrier)) : y ∈ image X W Z π := by
  obtain ⟨w, hwW, hwy⟩ := hyπ
  have hπy : IsClosed ({π.left y} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace m)) := by
    simpa only [Set.image_singleton] using π.left.isClosedMap _ hy
  have hw : IsClosed ({w} : Set X.carrier) := Closed.FiberPoints.closed π.left w (hwy.symm ▸ hπy)
  obtain ⟨a, ha, haw, hay⟩ := Support.PairClosedPoints.exists_pair X W Z w y hw hy hwW hyZ
  have heq : (Support.Pair.first X W Z ≫ π).left a = (Support.Pair.second X W Z ≫ π).left a := by
    change π.left ((Support.Pair.first X W Z).left a) = π.left ((Support.Pair.second X W Z).left a)
    rw [haw, hay]
    exact hwy
  have haI : a ∈ Generic.Finite.Projection.coincidence X W Z π :=
    Closed.Equalizer.mem_of_closed (Support.Pair.first X W Z ≫ π) (Support.Pair.second X W Z ≫ π) a ha heq
  have haD : a ∉ Support.PairIncidenceStep.diagonal X W Z := by
    intro hd
    have he := Closed.Equalizer.eq_of_mem (Support.Pair.first X W Z) (Support.Pair.second X W Z) a hd
    have hwy' : w = y := haw.symm.trans (he.trans hay)
    exact hyW (hwy' ▸ hwW)
  have har : a ∈ removed X W Z π := by
    change a ∈ (ClosedDifferenceDimension.away (Generic.Finite.Projection.coincidence X W Z π)
      (Support.PairIncidenceStep.diagonal X W Z) : Set (Support.Pair.space X W Z))
    rw [ClosedDifferenceDimension.away_coe]
    exact subset_closure ⟨haI, haD⟩
  exact ⟨a, har, hay⟩

theorem residual_subset :
    (ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) W : Set X.carrier) ⊆
      π.left ⁻¹' (π.left '' (W : Set X.carrier)) := by
  apply closure_minimal Set.sdiff_subset
  exact (π.left.isClosedMap _ W.isClosed).preimage π.left.continuous

theorem residual_inter_subset :
    ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) W ⊓ ⟨Z, Z.isClosed⟩ ≤
      image X W Z π ⊔ ⟨W, W.isClosed⟩ := by
  apply Projection.ProjectionCoincidence.closed_subset X.structureMap
  intro y hy hc
  by_cases hw : y ∈ W
  · exact Or.inr hw
  · exact Or.inl (mem_image X W Z π y hc hy.2 hw (residual_subset X W π hy.1))

theorem support_bound_outside (d : ℕ)
    (hI : ∀ C : IrreducibleCloseds (Support.Pair.space X W Z), (C : Set (Support.Pair.space X W Z)) ⊆ Generic.Finite.Projection.coincidence X W Z π →
      ¬ (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X W Z) + m ≤ d)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆
      (ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) W : Set X.carrier) ∩
        (Z : Set X.carrier))
    (hCW : ¬ (C : Set X.carrier) ⊆ W) : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.structureMap + m ≤ d := by
  have hu : (C : Set X.carrier) ⊆ (image X W Z π : Set X.carrier) ∪ W :=
    hC.trans (residual_inter_subset X W Z π)
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp C.isIrreducible.isPreirreducible
    (image X W Z π) W (image X W Z π).isClosed W.isClosed hu with hi | hw
  · exact bound X W Z π d hI C hi
  · exact (hCW hw).elim

end IncidenceImage

end

section

/-! A generic finite projection improves every excess intersection
of its residuals by one, simultaneously for a finite family of support pairs. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Step

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

def intersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier) : Closeds X.carrier :=
  ⟨(W : Set X.carrier) ∩ (Z : Set X.carrier), W.isClosed.inter Z.isClosed⟩

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ : Type} [Finite τ] (W Z : τ → IrreducibleCloseds X.carrier)
    (hW : ∀ t, 1 ≤ X.supportCodimension (W t)) (k : τ → ℕ)
    (hbound : ∀ t, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ intersection X (W t) (Z t) → k t ≤ X.supportCodimension C) :
    ∃ π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m), IsFinite π.left ∧
      ∀ t, ∀ C : IrreducibleCloseds X.carrier,
        (C : Set X.carrier) ⊆
          (ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) (W t) : Set X.carrier) ∩
            (Z t : Set X.carrier) →
        min (X.supportCodimension (W t) + X.supportCodimension (Z t)) (k t + 1) ≤ X.supportCodimension C := by
  classical
  let : JacobsonSpace X.carrier := LocallyOfFiniteType.jacobsonSpace X.structureMap
  let S t := intersection X (W t) (Z t)
  let (t : τ) : NoetherianSpace (S t) := NoetherianSpace.set (S t : Set X.carrier)
  let (t : τ) : Finite (irreducibleComponents (S t)) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S t)).to_subtype
  let J := Σ t : τ, irreducibleComponents (S t)
  have hpoints : ∀ j : J, ∃ x : X.carrier,
      x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j.1) j.2 ∧ IsClosed {x} := by
    intro j
    let D := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S j.1) j.2
    obtain ⟨x, hxD, hxc⟩ := nonempty_inter_closedPoints D.isIrreducible.nonempty D.isClosed.isLocallyClosed
    exact ⟨x, hxD, hxc⟩
  choose x hxD hxc using hpoints
  obtain ⟨π, hfinite, havoid, hI⟩ := Generic.Residual.Projection.exists_projection X m W Z
    (fun j : J => W j.1) (fun j => hW j.1) x hxc
  let := hfinite
  refine ⟨π, hfinite, ?_⟩
  intro t C hC
  by_cases hCW : (C : Set X.carrier) ⊆ W t
  · have hCS : (C : Set X.carrier) ⊆ S t := fun y hy => ⟨hCW hy, (hC hy).2⟩
    obtain ⟨b, hb⟩ := Supports.closedComponentSupport_covers X.carrier (S t) C hCS
    let D := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (S t) b
    have hne : C ≠ D := by
      intro he
      exact havoid ⟨t, b⟩ ((hC (he ▸ hxD ⟨t, b⟩)).1)
    have hlt := Supports.codimension_strictAnti X m (lt_of_le_of_ne hb hne)
    change X.supportCodimension D < X.supportCodimension C at hlt
    have hk := hbound t D (Supports.closedComponentSupport_subset X.carrier (S t) b)
    omega
  · have hd := IncidenceImage.support_bound_outside X (W t) (Z t) π
      (Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap)
      (hI t) C hC hCW
    have hdimW := Grading.supportDimension_add_codimension X m (W t)
    have hdimZ := Grading.supportDimension_add_codimension X m (Z t)
    have hdimC := Grading.supportDimension_add_codimension X m C
    omega

end Step

end

/-! The residual improvement criterion for a fixed projection,
using its actual incidence bound and avoided component witnesses. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Criterion

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

theorem bound (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsFinite π.left]
    (W Z : IrreducibleCloseds X.carrier) (k : ℕ)
    (hbound : ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ Step.intersection X W Z → k ≤ X.supportCodimension C)
    (hI : ∀ C : IrreducibleCloseds (Support.Pair.space X W Z),
      (C : Set (Support.Pair.space X W Z)) ⊆ Generic.Finite.Projection.coincidence X W Z π →
      ¬ (C : Set (Support.Pair.space X W Z)) ⊆ Support.PairIncidenceStep.diagonal X W Z →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X W Z) + m ≤
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap)
    (hcut : ∀ D : irreducibleComponents (Step.intersection X W Z),
      ∃ x ∈ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (Step.intersection X W Z) D,
        x ∉ ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) W)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆
      (ResidualAvoidance.Projection.residual (Generic.Residual.Projection.map π) W : Set X.carrier) ∩ (Z : Set X.carrier)) :
    min (X.supportCodimension W + X.supportCodimension Z) (k + 1) ≤ X.supportCodimension C := by
  by_cases hCW : (C : Set X.carrier) ⊆ W
  · have hCS : (C : Set X.carrier) ⊆ Step.intersection X W Z :=
      fun y hy => ⟨hCW hy, (hC hy).2⟩
    obtain ⟨b, hb⟩ := Supports.closedComponentSupport_covers X.carrier
      (Step.intersection X W Z) C hCS
    let D := CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier (Step.intersection X W Z) b
    obtain ⟨x, hxD, hxR⟩ := hcut b
    have hne : C ≠ D := by
      intro he
      exact hxR ((hC (he ▸ hxD)).1)
    have hlt := Supports.codimension_strictAnti X m (lt_of_le_of_ne hb hne)
    change X.supportCodimension D < X.supportCodimension C at hlt
    have hk := hbound D (Supports.closedComponentSupport_subset X.carrier (Step.intersection X W Z) b)
    omega
  · have hd := IncidenceImage.support_bound_outside X W Z π _ hI C hC hCW
    have hdimW := Grading.supportDimension_add_codimension X m W
    have hdimZ := Grading.supportDimension_add_codimension X m Z
    have hdimC := Grading.supportDimension_add_codimension X m C
    omega

end Criterion

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualIntersection
