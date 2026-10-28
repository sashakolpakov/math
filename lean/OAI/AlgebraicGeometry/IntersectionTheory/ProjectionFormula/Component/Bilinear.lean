import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Bilinear -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear

noncomputable section

section

/-! Proper meeting and the finite native intersection cycle commute
with inclusion of an actual integral component. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace PairCycle

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem pair_proper_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport p)
    (B : (X.componentVariety C).presentation.DimensionCycleSupport q) :
    Supports.ProperCycle.pairMeetsProperly X p q (Image.supportImage X C p A) (Image.supportImage X C q B) ↔
      Supports.ProperCycle.pairMeetsProperly (X.componentVariety C).presentation p q A B := by
  constructor
  · intro h D hD
    have hh := h (X.componentSupportImage C D) (by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, (hD hx).1, rfl⟩, ⟨x, (hD hx).2, rfl⟩⟩)
    rwa [Image.image_codimension] at hh
  · intro h D hD
    have hd : (D : Set X.carrier) ⊆ C.val :=
      fun x hx => X.componentSupportImage_subset C A.val (hD hx).1
    let E := X.componentSupportPreimage C D hd
    have he : (E : Set (X.componentVariety C).carrier) ⊆
        (A.val : Set (X.componentVariety C).carrier) ∩ B.val := by
      intro y hy
      have hh := hD hy
      obtain ⟨a, ha, hay⟩ := hh.1
      obtain ⟨b, hb, hby⟩ := hh.2
      exact ⟨(X.componentInclusion C).isOpenEmbedding.injective hay ▸ ha,
        (X.componentInclusion C).isOpenEmbedding.injective hby ▸ hb⟩
    have hh := h E he
    rw [← Image.image_codimension, X.componentSupportImage_preimage] at hh
    exact hh

theorem pairCycle_restrict_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport p)
    (B : (X.componentVariety C).presentation.DimensionCycleSupport q) :
    letI := Image.component_relativeDimension X m C
    CycleMaps.restrict X C (p + q) (Supports.ProperCycle.pairCycle X m p q (Image.supportImage X C p A) (Image.supportImage X C q B)) =
      Supports.ProperCycle.pairCycle (X.componentVariety C).presentation m p q A B := by
  let := Image.component_relativeDimension X m C
  by_cases h : Supports.ProperCycle.pairMeetsProperly (X.componentVariety C).presentation p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q _ _ ((pair_proper_image X C p q A B).mpr h),
      Supports.ProperCycle.pairCycle_apply _ m p q A B h]
    exact (Iff.multiplicity_image X m C A.val B.val D.val).symm
  · have hn := fun hh => h ((pair_proper_image X C p q A B).mp hh)
    rw [Supports.ProperCycle.pairCycle, dite_eq_right hn, map_zero, Supports.ProperCycle.pairCycle, dite_eq_right h]

theorem pairCycle_restrict_outside_left (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hA : ¬ (A.val : Set X.carrier) ⊆ C.val) :
    CycleMaps.restrict X C (p + q) (Supports.ProperCycle.pairCycle X m p q A B) = 0 := by
  by_cases hp : Supports.ProperCycle.pairMeetsProperly X p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q A B hp, Finsupp.zero_apply, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity]
    apply dite_eq_right
    intro hx
    exact hA (Principal.subset_of_mem X C A.val _ hx.1
      (X.componentSupportImage_subset C D.val
        (((X.componentSupportImage C D.val).isIrreducible.isGenericPoint_genericPoint
          (X.componentSupportImage C D.val).isClosed).mem)))
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right hp, map_zero]

theorem pairCycle_restrict_outside_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q)
    (hB : ¬ (B.val : Set X.carrier) ⊆ C.val) :
    CycleMaps.restrict X C (p + q) (Supports.ProperCycle.pairCycle X m p q A B) = 0 := by
  by_cases hp : Supports.ProperCycle.pairMeetsProperly X p q A B
  · ext D
    rw [CycleMaps.restrict_apply, Supports.ProperCycle.pairCycle_apply X m p q A B hp, Finsupp.zero_apply, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity]
    apply dite_eq_right
    intro hx
    exact hB (Principal.subset_of_mem X C B.val _ hx.2
      (X.componentSupportImage_subset C D.val
        (((X.componentSupportImage C D.val).isIrreducible.isGenericPoint_genericPoint
          (X.componentSupportImage C D.val).isClosed).mem)))
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right hp, map_zero]

end PairCycle

end

/-! The native finite intersection construction commutes with restriction
to every integral component, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear.PairCycle

theorem restrict_single_image (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (A : (X.componentVariety C).presentation.DimensionCycleSupport p) (r : ℚ) :
    CycleMaps.restrict X C p (Finsupp.single (Image.supportImage X C p A) r) = Finsupp.single A r := by
  rw [← CycleMaps.embed_single, CycleMaps.restrict_embed]

theorem restrict_single_outside (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (A : X.DimensionCycleSupport p) (r : ℚ) (hA : ¬ (A.val : Set X.carrier) ⊆ C.val) :
    CycleMaps.restrict X C p (Finsupp.single A r) = 0 := by
  ext D
  rw [CycleMaps.restrict_apply, Finsupp.single_apply, Finsupp.zero_apply]
  apply ite_eq_right
  intro he
  have he' := congrArg Subtype.val he
  apply hA
  rw [he']
  exact X.componentSupportImage_subset C D.val

theorem pairCycle_restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) :
    letI := Image.component_relativeDimension X m C
    CycleMaps.restrict X C (p + q) (Supports.ProperCycle.pairCycle X m p q A B) =
      Supports.ProperCycle.intersectionBilinear (X.componentVariety C).presentation m p q
        (CycleMaps.restrict X C p (Finsupp.single A 1)) (CycleMaps.restrict X C q (Finsupp.single B 1)) := by
  let := Image.component_relativeDimension X m C
  by_cases hA : (A.val : Set X.carrier) ⊆ C.val
  · by_cases hB : (B.val : Set X.carrier) ⊆ C.val
    · obtain ⟨A', rfl⟩ : ∃ A', Image.supportImage X C p A' = A :=
        ⟨Image.supportPreimage X C p A hA, Image.supportImage_preimage X C p A hA⟩
      obtain ⟨B', rfl⟩ : ∃ B', Image.supportImage X C q B' = B :=
        ⟨Image.supportPreimage X C q B hB, Image.supportImage_preimage X C q B hB⟩
      rw [PairCycle.pairCycle_restrict_image, restrict_single_image, restrict_single_image]
      simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, one_smul]
    · rw [PairCycle.pairCycle_restrict_outside_right X m C p q A B hB,
        restrict_single_outside X C q B 1 hB, map_zero]
  · rw [PairCycle.pairCycle_restrict_outside_left X m C p q A B hA,
      restrict_single_outside X C p A 1 hA, map_zero, LinearMap.zero_apply]

theorem bilinear_single_single (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A : X.DimensionCycleSupport p)
    (B : X.DimensionCycleSupport q) (r s : ℚ) :
    Supports.ProperCycle.intersectionBilinear X m p q (Finsupp.single A r) (Finsupp.single B s) =
      r • s • Supports.ProperCycle.pairCycle X m p q A B := by
  simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, LinearMap.smul_apply]

theorem restrict_bilinear (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (C : irreducibleComponents X.carrier) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    letI := Image.component_relativeDimension X m C
    CycleMaps.restrict X C (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) =
      Supports.ProperCycle.intersectionBilinear (X.componentVariety C).presentation m p q (CycleMaps.restrict X C p a) (CycleMaps.restrict X C q b) := by
  let := Image.component_relativeDimension X m C
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single A r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | single B s =>
      rw [bilinear_single_single, map_smul, map_smul, pairCycle_restrict]
      have hr : Finsupp.single A r = r • Finsupp.single A (1 : ℚ) := by simp
      have hs : Finsupp.single B s = s • Finsupp.single B (1 : ℚ) := by simp
      rw [hr, hs, map_smul, map_smul, map_smul, LinearMap.smul_apply, map_smul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear
