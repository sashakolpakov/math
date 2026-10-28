import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.Multiplicity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport

/-! # Support Bound -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SupportBound

noncomputable section

section

/-! The cone intersection on an integral smooth projective scheme
is a finite cycle with the exact ambient Tor coefficients. Subtracting
the original support leaves a cycle on the residual closed set. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace IntegralCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
  (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
  (p : ℕ) (W : X.DimensionCycleSupport p)

def cone : IrreducibleCloseds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension) :=
  Projective.ConeSupport.support L hL (Projection.FiniteProjective.FromForms.map X m L h (CycleClass.Thom.IntersectionGeometry.supportPoint W.val))

def intersection : Closeds X.carrier :=
  ⟨X.embedding ⁻¹' (cone X m L hL h p W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)),
    (cone X m L hL h p W).isClosed.preimage X.embedding.continuous⟩

variable [IsIntegral X.carrier]

def coefficient (C : X.DimensionCycleSupport p) : ℚ :=
  CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity (Projective.Dimension.SpacePresentation.presentation X.ambientDimension)
    (cone X m L hL h p W) (Closed.ImmersionSupport.support X.embedding)
    (Multiplicity.IntegralProjection.imageSupport X C.val)

theorem coefficient_nonzero (C : X.DimensionCycleSupport p)
    (hC : coefficient X m L hL h p W C ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ intersection X m L hL h p W := by
  by_contra hn
  apply hC
  apply dite_eq_right
  intro hm
  have he := Multiplicity.IntegralProjection.image_point X C.val
  have ha := hm.1
  rw [he] at ha
  exact hn ha

variable [SmoothOfRelativeDimension m X.structureMap]

theorem coefficients_finite : (Function.support (coefficient X m L hL h p W)).Finite := by
  apply (Supports.finite_supports_in_proper_closed X m p
    (intersection X m L hL h p W) ?_).subset
  · intro C hC
    exact coefficient_nonzero X m L hL h p W C hC
  · intro C hC
    rw [← W.property]
    exact Projective.ConeCodimension.intersection_bound X m L hL h W.val C hC

def cycle : X.RationalDimensionCycle p :=
  Finsupp.ofSupportFinite (coefficient X m L hL h p W) (coefficients_finite X m L hL h p W)

theorem cycle_apply (C : X.DimensionCycleSupport p) :
    cycle X m L hL h p W C = coefficient X m L hL h p W C := rfl

theorem cycle_supported : CycleSupport.SupportedOn X p (cycle X m L hL h p W)
    (intersection X m L hL h p W) := by
  intro C hC
  apply (Supports.supportPoint_mem_iff_subset _ C.val).mp
  exact coefficient_nonzero X m L hL h p W C (Finsupp.mem_support_iff.mp hC)

def residual : X.RationalDimensionCycle p := cycle X m L hL h p W - Finsupp.single W 1

theorem decomposition : cycle X m L hL h p W = Finsupp.single W 1 + residual X m L hL h p W := by
  unfold residual
  abel

theorem original_coefficient (U : X.carrier.Opens) [Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)]
    (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier)) (hxU : x ∈ U) :
    cycle X m L hL h p W W = 1 :=
  Multiplicity.IntegralProjection.multiplicity_one X m L hL h W.val U x hxW hxU

theorem residual_supported (U : X.carrier.Opens) [Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)]
    (x : X.carrier) (hxW : x ∈ (W.val : Set X.carrier)) (hxU : x ∈ U) :
    CycleSupport.SupportedOn X p (residual X m L hL h p W)
      (ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) W.val) := by
  intro C hC
  have hne : C ≠ W := by
    intro he
    subst C
    have hc := Finsupp.mem_support_iff.mp hC
    apply hc
    rw [residual, Finsupp.sub_apply, Finsupp.single_eq_same, original_coefficient X m L hL h p W U x hxW hxU, sub_self]
  have hc : C ∈ (cycle X m L hL h p W).support := by
    rw [Finsupp.mem_support_iff]
    have ht := Finsupp.mem_support_iff.mp hC
    rw [residual, Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero] at ht
    exact ht
  have hη : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (W.val : Set X.carrier) := by
    intro hm
    let S : Closeds X.carrier := ⟨(W.val : Set X.carrier), W.val.isClosed⟩
    have hle : C.val ≤ W.val :=
      (Supports.supportPoint_mem_iff_subset S C.val).mp hm
    have hlt := Supports.codimension_strictAnti X m
      (lt_of_le_of_ne hle (fun he => hne (Subtype.ext he)))
    rw [W.property, C.property] at hlt
    exact lt_irrefl p hlt
  apply (Supports.supportPoint_mem_iff_subset _ C.val).mp
  apply subset_closure
  refine ⟨?_, hη⟩
  have hm := coefficient_nonzero X m L hL h p W C (Finsupp.mem_support_iff.mp hc)
  change CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ X.embedding ⁻¹' (cone X m L hL h p W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) at hm
  exact Eq.mp (congrArg (fun S : Set X.carrier => CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ S)
    (Projective.ConePreimage.intersection X m L hL h W.val)) hm

end IntegralCycle

end

/-! Proper bounds for the original support and the full residual
closed set control the entire cone intersection, including components
that might carry zero native cycle coefficient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem saturated (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {Y : Scheme} (π : X.carrier ⟶ Y)
    (W B : IrreducibleCloseds X.carrier) (k : ℕ)
    (hW : ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W : Set X.carrier) ∩ (B : Set X.carrier) → k ≤ X.supportCodimension C)
    (hR : ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (ResidualAvoidance.Projection.residual π W : Set X.carrier) ∩ (B : Set X.carrier) →
        k ≤ X.supportCodimension C)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ (π ⁻¹' (π '' (W : Set X.carrier))) ∩ (B : Set X.carrier)) :
    k ≤ X.supportCodimension C := by
  have hη : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (C : Set X.carrier) := (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem
  by_cases hw : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X.carrier)
  · have hCW : (C : Set X.carrier) ⊆ W :=
      (Supports.supportPoint_mem_iff_subset ⟨W, W.isClosed⟩ C).mp hw
    exact hW C (fun z hz => ⟨hCW hz, (hC hz).2⟩)
  · have hr : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (ResidualAvoidance.Projection.residual π W : Set X.carrier) :=
      subset_closure ⟨(hC hη).1, hw⟩
    have hCR := (Supports.supportPoint_mem_iff_subset
      (ResidualAvoidance.Projection.residual π W) C).mp hr
    exact hR C (fun z hz => ⟨hCR hz, (hC hz).2⟩)

theorem cone (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal)
    (p q : ℕ) (W : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hW : ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ (W.val : Set X.carrier) ∩ (B.val : Set X.carrier) → p + q ≤ X.supportCodimension C)
    (hR : ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆
        (ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) W.val : Set X.carrier) ∩
        (B.val : Set X.carrier) → p + q ≤ X.supportCodimension C)
    (C : IrreducibleCloseds X.carrier)
    (hC : (C : Set X.carrier) ⊆ (IntegralCycle.intersection X m L hL h p W : Set X.carrier) ∩
      (B.val : Set X.carrier)) : p + q ≤ X.supportCodimension C := by
  apply saturated X (Projection.FiniteProjective.FromForms.map X m L h) W.val B.val (p + q) hW hR C
  change (C : Set X.carrier) ⊆
    (X.embedding ⁻¹' (IntegralCycle.cone X m L hL h p W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) ∩
      (B.val : Set X.carrier) at hC
  have he : X.embedding ⁻¹' (IntegralCycle.cone X m L hL h p W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) =
      Projection.FiniteProjective.FromForms.map X m L h ⁻¹' (Projection.FiniteProjective.FromForms.map X m L h '' (W.val : Set X.carrier)) :=
    Projective.ConePreimage.intersection X m L hL h W.val
  rw [he] at hC
  exact hC

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.SupportBound
