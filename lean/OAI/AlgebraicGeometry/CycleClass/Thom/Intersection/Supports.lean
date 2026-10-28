import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

/-! # Supports -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports

noncomputable section

/-! In a proper intersection, a support of the prescribed codimension
is an irreducible component of the closed intersection. Hence there are
only finitely many possible nonzero intersection coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

theorem closedComponentSupport_covers (X : Scheme) (S : Closeds X)
    (C : IrreducibleCloseds X) (hC : (C : Set X) ⊆ S) :
    ∃ D : irreducibleComponents S, (C : Set X) ⊆ IntersectionGeometry.closedComponentSupport X S D := by
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
    (D : irreducibleComponents S) : (IntersectionGeometry.closedComponentSupport X S D : Set X) ⊆ S := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem supportDimension_add_codimension (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (W : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W X.structureMap + X.supportCodimension W =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent W)).structureMap := by
  let C := X.supportComponent W
  let Z := X.componentSupportPreimage C W (X.support_subset_component W)
  have hW : X.componentSupportImage C Z = W := X.componentSupportImage_preimage C W _
  have h := Geometric.DimensionCycles.supportDimension_add_dimensionCodimension (X.componentVariety C) Z
  rw [← X.componentSupportImage_transcendenceDimension C Z,
    ← X.supportCodimension_componentSupportImage C Z, hW] at h
  exact h

theorem codimension_strictAnti (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    StrictAnti X.supportCodimension := by
  intro A B hAB
  have ht := Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono X.structureMap hAB
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap <
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension B X.structureMap at ht
  have hc : X.supportComponent A = X.supportComponent B :=
    X.supportComponent_eq_of_subset A (X.supportComponent B)
      (fun _ hx => X.support_subset_component B (hAB.le hx))
  have ha := supportDimension_add_codimension X A
  have hb := supportDimension_add_codimension X B
  rw [hc] at ha
  omega

theorem support_eq_component (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (d : ℕ) (S : Closeds X.carrier)
    (hproper : ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ S → d ≤ X.supportCodimension C)
    (C : X.DimensionCycleSupport d) (hC : (C.val : Set X.carrier) ⊆ S) :
    ∃ D : irreducibleComponents S, IntersectionGeometry.closedComponentSupport X.carrier S D = C.val := by
  obtain ⟨D, hD⟩ := closedComponentSupport_covers X.carrier S C.val hC
  have hle : C.val ≤ IntersectionGeometry.closedComponentSupport X.carrier S D := hD
  have he : C.val = IntersectionGeometry.closedComponentSupport X.carrier S D := by
    by_contra hn
    have ht := codimension_strictAnti X (lt_of_le_of_ne hle hn)
    have hd := hproper (IntersectionGeometry.closedComponentSupport X.carrier S D)
      (closedComponentSupport_subset X.carrier S D)
    rw [C.property] at ht
    omega
  exact ⟨D, he.symm⟩

theorem supportPoint_mem_iff_subset {X : Scheme} (S : Closeds X) (C : IrreducibleCloseds X) :
    IntersectionGeometry.supportPoint C ∈ S ↔ (C : Set X) ⊆ S := by
  constructor
  · intro h
    have hc : closure {IntersectionGeometry.supportPoint C} = (C : Set X) :=
      congrArg (fun A : IrreducibleCloseds X => (A : Set X))
        (irreducibleSetEquivPoints.symm_apply_apply C)
    rw [← hc]
    exact S.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  · intro h
    exact h (C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem

theorem finite_supports_in_proper_closed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (d : ℕ) (S : Closeds X.carrier)
    (hproper : ∀ C : IrreducibleCloseds X.carrier, (C : Set X.carrier) ⊆ S → d ≤ X.supportCodimension C) :
    {C : X.DimensionCycleSupport d | IntersectionGeometry.supportPoint C.val ∈ S}.Finite := by
  let : NoetherianSpace S := NoetherianSpace.set (S : Set X.carrier)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  have hf : (Set.range (IntersectionGeometry.closedComponentSupport X.carrier S)).Finite := Set.finite_range _
  apply Set.Finite.of_finite_image (f := fun C : X.DimensionCycleSupport d => C.val)
    (hf.subset ?_) Subtype.val_injective.injOn
  rintro _ ⟨C, hC, rfl⟩
  exact support_eq_component X d S hproper C ((supportPoint_mem_iff_subset S C.val).mp hC)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Supports
