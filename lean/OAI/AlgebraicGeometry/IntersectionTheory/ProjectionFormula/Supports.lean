import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Grading

/-! # Supports -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! In a proper intersection, a support of the prescribed codimension
is an irreducible component of the closed intersection. Hence there are
only finitely many possible nonzero intersection coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem closedComponentSupport_covers (X : Scheme) (S : Closeds X)
    (C : IrreducibleCloseds X) (hC : (C : Set X) ⊆ S) :
    ∃ D : irreducibleComponents S, (C : Set X) ⊆ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S D := by
  let : IrreducibleSpace C := isIrreducible_iff_irreducibleSpace.mp C.isIrreducible
  let j : C → S := fun x => ⟨x, hC x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hi : IsIrreducible (j '' (Set.univ : Set C)) :=
    (IrreducibleSpace.isIrreducible_univ C).image j hj.continuousOn
  obtain ⟨D, hD, hCD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hi
  refine ⟨⟨D, hD⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hC hx⟩, hCD ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩, rfl⟩

theorem closedComponentSupport_subset (X : Scheme) (S : Closeds X)
    (D : irreducibleComponents S) : (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X S D : Set X) ⊆ S := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem codimension_strictAnti (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] : StrictAnti X.supportCodimension := by
  intro A B hAB
  have ht := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap hAB
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap < Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap at ht
  have ha := Grading.supportDimension_add_codimension X m A
  have hb := Grading.supportDimension_add_codimension X m B
  omega

theorem support_eq_component (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier)
    (hproper : ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ S → d ≤ X.supportCodimension C)
    (C : X.DimensionCycleSupport d) (hC : (C.val : Set X.carrier) ⊆ S) :
    ∃ D : irreducibleComponents S, CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D = C.val := by
  obtain ⟨D, hD⟩ := closedComponentSupport_covers X.carrier S C.val hC
  have hle : C.val ≤ CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D := hD
  have he : C.val = CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D := by
    by_contra hn
    have ht := codimension_strictAnti X m (lt_of_le_of_ne hle hn)
    have hd := hproper (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S D)
      (closedComponentSupport_subset X.carrier S D)
    rw [C.property] at ht
    omega
  exact ⟨D, he.symm⟩

theorem supportPoint_mem_iff_subset {X : Scheme} (S : Closeds X) (C : IrreducibleCloseds X) :
    CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ S ↔ (C : Set X) ⊆ S := by
  constructor
  · intro h
    have hc : closure {CycleClass.Thom.IntersectionGeometry.supportPoint C} = (C : Set X) :=
      congrArg (fun A : IrreducibleCloseds X => (A : Set X))
        (irreducibleSetEquivPoints.symm_apply_apply C)
    rw [← hc]
    exact S.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  · intro h
    exact h (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem

theorem finite_supports_in_proper_closed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m d : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (S : Closeds X.carrier)
    (hproper : ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ S → d ≤ X.supportCodimension C) :
    {C : X.DimensionCycleSupport d | CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ S}.Finite := by
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  have hf : (Set.range (CycleClass.Thom.IntersectionGeometry.closedComponentSupport X.carrier S)).Finite := Set.finite_range _
  apply Set.Finite.of_finite_image (f := fun C : X.DimensionCycleSupport d => C.val)
    (hf.subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨C, hC, rfl⟩
  exact support_eq_component X m d S hproper C ((supportPoint_mem_iff_subset S C.val).mp hC)

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

/-! Properly meeting cycles have an actual finite intersection cycle
with exactly ThomClass's local Tor coefficients. The finite construction is
bilinear before imposing the proper-meeting condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

def pairMeetsProperly (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) : Prop :=
  ∀ C : IrreducibleCloseds X.carrier,
    (C : Set X.carrier) ⊆ (A.val : Set X.carrier) ∩ (B.val : Set X.carrier) →
      p + q ≤ X.supportCodimension C

theorem pair_coefficients_finite (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (h : pairMeetsProperly X p q A B) :
    (Function.support (fun C : X.DimensionCycleSupport (p + q) =>
      CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val)).Finite := by
  let S : Closeds X.carrier := ⟨(A.val : Set X.carrier) ∩ B.val, A.val.isClosed.inter B.val.isClosed⟩
  apply (finite_supports_in_proper_closed X m (p + q) S h).subset
  intro C hC
  by_contra hc
  exact hC (dite_eq_right hc)

def pairCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) :
    X.RationalDimensionCycle (p + q) :=
  if h : pairMeetsProperly X p q A B then
    Finsupp.ofSupportFinite (fun C => CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val)
      (pair_coefficients_finite X m p q A B h)
  else 0

theorem pairCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (h : pairMeetsProperly X p q A B) (C : X.DimensionCycleSupport (p + q)) :
    pairCycle X m p q A B C = CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val := by
  rw [pairCycle, dite_eq_left h]
  rfl

def intersectionBilinear (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    X.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle q →ₗ[ℚ]
      X.RationalDimensionCycle (p + q) :=
  Finsupp.linearCombination ℚ (fun A => Finsupp.linearCombination ℚ (pairCycle X m p q A))

theorem intersectionBilinear_isProper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b (intersectionBilinear X m p q a b) := by
  refine ⟨h, ?_⟩
  intro C
  simp only [intersectionBilinear, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  rw [pairCycle_apply X m p q A B (h A hA B hB) C]
  ring

theorem properIntersection_exists_unique (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (h : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a b) :
    ∃! c : X.RationalDimensionCycle (p + q), CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b c := by
  refine ⟨intersectionBilinear X m p q a b, intersectionBilinear_isProper X m p q a b h, ?_⟩
  intro c hc
  exact CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X p q hc (intersectionBilinear_isProper X m p q a b h)

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

end

end OAI
