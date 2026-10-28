import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map
import OAI.AlgebraicGeometry.Divisors.LineBundles.Ord

/-! # Closed Section Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle

noncomputable section

section

/-!
# ProjectionFormula: principal-divisor generators as constructed finite cycles

The ThomClass coefficient relation is identified with the degree component of
the actual finite principal divisor on the integral support. Finiteness
comes from Divisors, independently of any Chow operation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

theorem degreeComponent_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (c : X.carrier →₀ ℚ) (C : X.DimensionCycleSupport p) :
    CyclePushforward.degreeComponent X p c C = c (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]
  | single x a =>
    rw [CyclePushforward.degreeComponent, Finsupp.linearCombination_single, Finsupp.smul_apply,
      CycleClass.Thom.IntersectionGeometry.supportInDegree_apply]
    have he : irreducibleSetEquivPoints.symm x = C.val ↔ x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val :=
      irreducibleSetEquivPoints.symm_apply_eq
    rw [he]
    by_cases hx : x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val
    · subst x
      simp
    · simp [hx]

theorem residueDegree_immersion {A B : Scheme} (i : A ⟶ B)
    [SurjectiveOnStalks i] (x : A) : i.residueDegree x = 1 := by
  have h := Support.Map.residueDegree_post_immersion (𝟙 A) i x
  simpa only [Category.id_comp, Scheme.Hom.residueDegree_id] using h

theorem pointPushforward_closedImmersion {A B : Scheme} (i : A ⟶ B)
    [IsClosedImmersion i] (c : A →₀ ℚ) :
    CyclePushforward.pointPushforward i c =
      Finsupp.embDomain ⟨i, i.isClosedEmbedding.injective⟩ c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.embDomain_add, hc, hd]
  | single x a =>
    rw [CyclePushforward.pointPushforward_single, residueDegree_immersion]
    simp

/-- The rational principal divisor on the actual support, embedded into
the ambient scheme and projected to the requested codimension. -/
def principalCycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : X.RationalDimensionCycle p :=
  CyclePushforward.degreeComponent X p
    (Finsupp.embDomain ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
      ((Divisors.LineBundles.Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) f).mapRange
        (Int.castRingHom ℚ) (map_zero _)))

theorem principalCycle_apply (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (C : X.DimensionCycleSupport p) :
    principalCycle X p W f C = CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W f C.val := by
  rw [principalCycle, degreeComponent_apply]
  by_cases hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier)
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hx]
    conv_lhs => rw [← CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx]
    exact Finsupp.embDomain_apply_self _ _ _
  · rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hx]
    apply Finsupp.embDomain_of_notMem_range
    change CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W)
    simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hx

/-- Every nonzero rational function gives a finite generator in exactly
the coefficient relation used to define ThomClass's quotient. -/
theorem principalCycle_isPrincipalDivisor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) (hW : X.supportCodimension W + 1 = p)
    (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hf : f ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p (principalCycle X p W f) :=
  ⟨W, hW, f, hf, principalCycle_apply X p W f⟩

theorem isPrincipalDivisor_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (d : X.RationalDimensionCycle p) :
    CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p d ↔
      ∃ W : IrreducibleCloseds X.carrier, X.supportCodimension W + 1 = p ∧
        ∃ f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField,
          f ≠ 0 ∧ d = principalCycle X p W f := by
  constructor
  · rintro ⟨W, hW, f, hf, hd⟩
    exact ⟨W, hW, f, hf, Finsupp.ext (fun C =>
      (hd C).trans (principalCycle_apply X p W f C).symm)⟩
  · rintro ⟨W, hW, f, hf, rfl⟩
    exact principalCycle_isPrincipalDivisor X p W hW f hf

theorem principalCycle_eq_pushforward (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (W : IrreducibleCloseds X.carrier) (f : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    principalCycle X p W f = CyclePushforward.degreeComponent X p
      (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W)
        ((Divisors.LineBundles.Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) f).mapRange
          (Int.castRingHom ℚ) (map_zero _))) := by
  rw [pointPushforward_closedImmersion]
  rfl

end

/-! A cycle supported on a closed section is recovered exactly
by projection, with coefficient one from every residue-field map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme} (s : X ⟶ Y) [IsClosedImmersion s]

theorem reconstruct (c : Y →₀ ℚ) (hc : (c.support : Set Y) ⊆ Set.range s) :
    CyclePushforward.pointPushforward s (Finsupp.comapDomain s c s.isClosedEmbedding.injective.injOn) = c := by
  rw [pointPushforward_closedImmersion]
  exact Finsupp.embDomain_comapDomain hc

theorem projection (q : Y ⟶ X) (h : s ≫ q = 𝟙 X)
    (c : Y →₀ ℚ) (hc : (c.support : Set Y) ⊆ Set.range s) :
    CyclePushforward.pointPushforward q c = Finsupp.comapDomain s c s.isClosedEmbedding.injective.injOn := by
  calc
    CyclePushforward.pointPushforward q c = CyclePushforward.pointPushforward q
        (CyclePushforward.pointPushforward s (Finsupp.comapDomain s c s.isClosedEmbedding.injective.injOn)) :=
      congrArg (CyclePushforward.pointPushforward q) (reconstruct s c hc).symm
    _ = _ := by
      rw [← LinearMap.comp_apply, ← CyclePushforward.pointPushforward_comp, h, CyclePushforward.pointPushforward_id, LinearMap.id_apply]

theorem apply (q : Y ⟶ X) (h : s ≫ q = 𝟙 X)
    (c : Y →₀ ℚ) (hc : (c.support : Set Y) ⊆ Set.range s) (x : X) :
    CyclePushforward.pointPushforward q c x = c (s x) := by
  rw [projection s q h c hc]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle
