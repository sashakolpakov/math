import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Iff
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.DivisorRestriction

/-! # Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal

noncomputable section

section

/-! Restriction to an actual open component preserves principal-divisor
relations, using the isomorphism of the reduced support schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

theorem coefficient_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (W D : IrreducibleCloseds (X.componentVariety C).carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (X.componentSupportImage C W)).functionField) :
    CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient (X.componentVariety C).presentation W
      (Divisor.DivisorRestriction.openFieldMap (X.componentSupportSchemeIso C W).hom f) D =
    CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X (X.componentSupportImage C W) f (X.componentSupportImage C D) := by
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint D ∈ (W : Set (X.componentVariety C).carrier)
  · let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint D) h
    have hy : CycleClass.Geometric.GenericPoint.reducedSupportι W y = CycleClass.Thom.IntersectionGeometry.supportPoint D := CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ h
    have he : CycleClass.Geometric.GenericPoint.reducedSupportι (X.componentSupportImage C W) ((X.componentSupportSchemeIso C W).hom y) =
        CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) := by
      have hh := congrArg (fun i : CycleClass.Geometric.GenericPoint.reducedSupportScheme W ⟶ X.carrier => i y)
        (X.componentSupportSchemeIso_hom_inclusion C W)
      change _ = X.componentInclusion C (CycleClass.Geometric.GenericPoint.reducedSupportι W y) at hh
      rw [hy] at hh
      exact hh.trans (X.componentSupportImage_genericPoint C D).symm
    rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient_at_image _ _ _ _ y hy,
      CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient_at_image _ _ _ _ _ he,
      Divisor.DivisorRestriction.ord_openImmersion]
  · have hn : CycleClass.Thom.IntersectionGeometry.supportPoint (X.componentSupportImage C D) ∉
        (X.componentSupportImage C W : Set X.carrier) :=
      fun hh => h ((Iff.image_point_mem_iff X C W D).mp hh)
    rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right h, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hn]

theorem restrict_principal_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p : ℕ)
    (W : IrreducibleCloseds (X.componentVariety C).carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme (X.componentSupportImage C W)).functionField) :
    CycleMaps.restrict X C p (Principal.ClosedSectionCycle.principalCycle X p (X.componentSupportImage C W) f) =
      Principal.ClosedSectionCycle.principalCycle (X.componentVariety C).presentation p W
        (Divisor.DivisorRestriction.openFieldMap (X.componentSupportSchemeIso C W).hom f) := by
  ext D
  rw [CycleMaps.restrict_apply, Principal.ClosedSectionCycle.principalCycle_apply, Principal.ClosedSectionCycle.principalCycle_apply]
  exact (coefficient_image X C W D.val f).symm

theorem subset_of_mem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (W : IrreducibleCloseds X.carrier) (x : X.carrier) (hx : x ∈ (W : Set X.carrier))
    (hC : x ∈ C.val) : (W : Set X.carrier) ⊆ C.val := by
  let := X.stalk_isDomain x
  have he := Foundations.Scheme.LocalDomainComponents.irreducibleComponents_eq_of_mem_of_stalkDomain x (X.supportComponent W).property
    C.property (X.support_subset_component W hx) hC
  rw [← he]
  exact X.support_subset_component W

theorem restrict_principal_outside (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p : ℕ) (W : IrreducibleCloseds X.carrier)
    (hW : ¬ (W : Set X.carrier) ⊆ C.val) (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    CycleMaps.restrict X C p (Principal.ClosedSectionCycle.principalCycle X p W f) = 0 := by
  ext D
  rw [CycleMaps.restrict_apply, Principal.ClosedSectionCycle.principalCycle_apply, Finsupp.zero_apply, CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient]
  apply dite_eq_right
  intro hx
  apply hW (subset_of_mem X C W _ hx _)
  exact X.componentSupportImage_subset C D.val
    (((X.componentSupportImage C D.val).isIrreducible.isGenericPoint_genericPoint
      (X.componentSupportImage C D.val).isClosed).mem)

theorem restrict_preserves_relations (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p : ℕ) :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences (X.componentVariety C).presentation p).comap (CycleMaps.restrict X C p) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨W, hW, f, hf, rfl⟩ := (Principal.ClosedSectionCycle.isPrincipalDivisor_iff X p d).mp hd
  change CycleMaps.restrict X C p (Principal.ClosedSectionCycle.principalCycle X p W f) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences (X.componentVariety C).presentation p
  by_cases hC : (W : Set X.carrier) ⊆ C.val
  · obtain ⟨Z, rfl⟩ : ∃ Z, X.componentSupportImage C Z = W :=
      ⟨X.componentSupportPreimage C W hC, X.componentSupportImage_preimage C W hC⟩
    rw [restrict_principal_image]
    apply Submodule.subset_span
    apply Principal.ClosedSectionCycle.principalCycle_isPrincipalDivisor
    · rwa [Image.image_codimension] at hW
    · exact (map_ne_zero (Divisor.DivisorRestriction.openFieldMap (X.componentSupportSchemeIso C Z).hom).hom).mpr hf
  · rw [restrict_principal_outside X C p W hC f]
    exact Submodule.zero_mem _

end

section

/-! Rational equivalence of native graded cycles can be tested separately
on the actual integral components. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace CycleDecomposition

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

theorem embed_apply_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : (X.componentVariety C).presentation.RationalDimensionCycle p)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport p) :
    CycleMaps.embed X C p a (Image.supportImage X C p A) = a A :=
  Finsupp.mapDomain_apply_of_injective (Image.supportImage_injective X C p) a A

theorem embed_apply_outside (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : (X.componentVariety C).presentation.RationalDimensionCycle p)
    (A : X.DimensionCycleSupport p) (h : ¬ (A.val : Set X.carrier) ⊆ C.val) :
    CycleMaps.embed X C p a A = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨B, rfl⟩
  exact h (X.componentSupportImage_subset C B.val)

theorem embed_restrict_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : X.RationalDimensionCycle p) (A : X.DimensionCycleSupport p) :
    CycleMaps.embed X C p (CycleMaps.restrict X C p a) A = if X.supportComponent A.val = C then a A else 0 := by
  by_cases h : X.supportComponent A.val = C
  · rw [ite_eq_left h]
    have ha : (A.val : Set X.carrier) ⊆ C.val := h ▸ X.support_subset_component A.val
    have he := Image.supportImage_preimage X C p A ha
    conv_lhs => rw [← he]
    rw [embed_apply_image, CycleMaps.restrict_apply, he]
  · rw [ite_eq_right h]
    exact embed_apply_outside X C p _ A (fun ha => h (X.supportComponent_eq_of_subset A.val C ha))

theorem sum_embed_restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    [Fintype (irreducibleComponents X.carrier)] (a : X.RationalDimensionCycle p) :
    ∑ C : irreducibleComponents X.carrier, CycleMaps.embed X C p (CycleMaps.restrict X C p a) = a := by
  ext A
  simp only [Finsupp.finsetSum_apply, embed_restrict_apply]
  simp

theorem relations_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : X.RationalDimensionCycle p) :
    a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X p ↔ ∀ C : irreducibleComponents X.carrier,
      CycleMaps.restrict X C p a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences (X.componentVariety C).presentation p := by
  constructor
  · intro ha C
    exact restrict_preserves_relations X C p ha
  · intro ha
    let := Fintype.ofFinite (irreducibleComponents X.carrier)
    rw [← sum_embed_restrict X p a]
    exact Submodule.sum_mem _ fun C _ => CycleMaps.embed_preserves_relations X m C p (ha C)

theorem rationallyEquivalent_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a b : X.RationalDimensionCycle p) :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X p a b ↔ ∀ C : irreducibleComponents X.carrier,
      CycleClass.Thom.IntersectionGeometry.RationallyEquivalent (X.componentVariety C).presentation p (CycleMaps.restrict X C p a) (CycleMaps.restrict X C p b) := by
  simp only [CycleClass.Thom.IntersectionGeometry.RationallyEquivalent, relations_iff X m p, map_sub]

end CycleDecomposition

end

/-! The native cycle restriction and embedding maps form a direct
sum over the actual disjoint integral components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Sum

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

theorem restrict_embed_other (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C D : irreducibleComponents X.carrier)
    (p : ℕ) (a : (X.componentVariety D).presentation.RationalDimensionCycle p) (hCD : C ≠ D) :
    CycleMaps.restrict X C p (CycleMaps.embed X D p a) = 0 := by
  ext W
  rw [CycleMaps.restrict_apply, Finsupp.zero_apply]
  apply CycleDecomposition.embed_apply_outside
  intro hW
  have hC := X.supportComponent_eq_of_subset (Image.supportImage X C p W).val C
    (X.componentSupportImage_subset C W.val)
  have hD := X.supportComponent_eq_of_subset (Image.supportImage X C p W).val D hW
  exact hCD (hC.symm.trans hD)

theorem restrict_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    [Fintype (irreducibleComponents X.carrier)]
    (a : ∀ C : irreducibleComponents X.carrier, (X.componentVariety C).presentation.RationalDimensionCycle p)
    (C : irreducibleComponents X.carrier) :
    CycleMaps.restrict X C p (∑ D, CycleMaps.embed X D p (a D)) = a C := by
  rw [map_sum]
  rw [Finset.sum_eq_single C]
  · exact CycleMaps.restrict_embed X C p (a C)
  · intro D _ hD
    exact restrict_embed_other X C D p (a D) hD.symm
  · intro h
    exact (h (Finset.mem_univ C)).elim

end Sum

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal
