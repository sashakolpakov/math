import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ExpectedComponentCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.PrincipalChartEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.CoverUnits
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartRestrictedCoefficient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.RestrictedPrincipalCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowMoving

/-! # Covered Principal Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalDescent

noncomputable section

section

/-! A cycle meeting the actual numerator and denominator support
cover properly annihilates the principal-divisor relation. The proof
constructs the restricted principal cycle from expected-dimensional
intersection components, even when the original supports meet improperly. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Relation

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
  [SmoothOfRelativeDimension m X.structureMap]
  (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
  (a : X.RationalDimensionCycle p)
  (hp : a ∈ Proper.SupportCycles.submodule X p (Principal.ChartSupportCover.family X m k W g hg))
  (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)

abbrev components := ExpectedComponentCycle.cycle X m p k A W

omit [SmoothOfRelativeDimension m X.structureMap] in
theorem in_W (D : X.DimensionCycleSupport (p + k)) (hD : D ∈ (components X m p k W A).support) :
    D.val ≤ W.val := (ExpectedComponentCycle.support_subset X m p k A W D hD).2

include hp hAa in
theorem units (D : (components X m p k W A).support) :
    ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (NestedGenericRestriction.point X.carrier D.val.val W.val (in_W X m p k W A D.val D.property)),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g :=
  Principal.CoverUnits.unit X m p k W g hg a hp A hAa D.val
    (ExpectedComponentCycle.support_subset X m p k A W D.val D.property).1
    (in_W X m p k W A D.val D.property)

def cycle : X.RationalDimensionCycle (p + (k + 1)) :=
  DegreeCast.cycle X (Nat.add_assoc p k 1)
    (General.RestrictedPrincipalCycle.cycle X (p + k) W.val (components X m p k W A)
      (in_W X m p k W A) g (units X m p k W g hg a hp A hAa))

theorem rationally_zero : cycle X m p k W g hg a hp A hAa ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) := by
  apply (DegreeCast.cycle_mem_relations X (Nat.add_assoc p k 1) _).mpr
  exact General.RestrictedPrincipalCycle.rationally_zero X (p + k) W.val (components X m p k W A)
    (in_W X m p k W A) g (units X m p k W g hg a hp A hAa)

theorem coefficient (C : X.DimensionCycleSupport (p + (k + 1))) :
    cycle X m p k W g hg a hp A hAa C =
      ∑ D : (components X m p k W A).support, (components X m p k W A) D.val *
        CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X D.val.val
          (NestedGenericRestriction.function X.carrier D.val.val W.val
            (in_W X m p k W A D.val D.property) g (units X m p k W g hg a hp A hAa D)) C.val := by
  rw [cycle, DegreeCast.cycle_apply, General.RestrictedPrincipalCycle.coefficient]

theorem in_chart (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal) :
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      cycle X m p k W g hg a hp A hAa C := by
  have h₁ := Proper.PrincipalChartEuler.component_sum X m p k W g hg a hp i A hAa A₀ hA C x hx hxA hvx
  have h₂ := ExpectedComponentCycle.reindex_at X m p k A W C (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) hx
    (Principal.ChartComponentSum.germ X W.val g hg (i, true) x)
    (Principal.ChartComponentSum.germ X W.val g hg (i, false) x)
  refine (h₁.trans h₂).trans ?_
  rw [coefficient]
  let c := components X m p k W A
  let w := fun D : X.DimensionCycleSupport (p + k) =>
    GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
      (Principal.ChartComponentSum.germ X W.val g hg (i, true) x) D.val -
    GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x)
      (Principal.ChartComponentSum.germ X W.val g hg (i, false) x) D.val
  refine (Finset.sum_coe_sort c.support (fun D => c D * w D)).symm.trans ?_
  apply Finset.sum_congr rfl
  intro D _
  apply congrArg (fun r : ℚ => c D.val * r)
  exact Principal.ChartRestrictedCoefficient.coefficient X m p k W g hg a hp i A hAa D.val
    (ExpectedComponentCycle.support_subset X m p k A W D.val D.property).1
    (in_W X m p k W A D.val D.property) (units X m p k W g hg a hp A hAa D) C.val x hx

theorem all_coefficients (C : X.DimensionCycleSupport (p + (k + 1))) :
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      cycle X m p k W g hg a hp A hAa C := by
  classical
  by_cases hpoint : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier) ∧ CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W.val : Set X.carrier)
  · obtain ⟨i, hi⟩ := Affine.ChartGerm.FiniteSupportCharts.covers X W.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hpoint.2
    rw [← (Affine.ChartGerm.FiniteSupportCharts.affine X W.val i).opensRange_fromSpec] at hi
    obtain ⟨x, hx⟩ := hi
    obtain ⟨vA, hvA, _, hvAx⟩ := Affine.SupportRepresentative.exists_prime (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) A.val x
      (hx.symm ▸ hpoint.1)
    have hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal := by
      apply (Affine.Prime.mem_iff (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) x).mp
      have hxW : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x ∈ (W.val : Set X.carrier) := hx.symm ▸ hpoint.2
      exact (congrArg (fun B : IrreducibleCloseds X.carrier => Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x ∈ (B : Set X.carrier))
        (Affine.ChartGerm.FiniteSupportCharts.prime_support X W.val i)).mpr hxW
    apply in_chart X m p k W g hg a hp A hAa i
      (Affine.SupportStalk.support (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) vA) ?_ C x hx
      (Affine.SupportStalk.mem (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i) vA x hvAx) hvx
    rw [Affine.SupportStalk.point]
    exact hvA
  · have hleft : (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
        (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) = 0 := by
      apply Finset.sum_eq_zero
      intro B hB
      have hBW := Support.Principal.subset X k W g B hB
      have hz : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val = 0 := by
        apply dite_eq_right
        intro h
        exact hpoint ⟨h.2, hBW h.1⟩
      exact (congrArg (fun r : ℚ => (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) B * r) hz).trans
        (mul_zero _)
    have hright : cycle X m p k W g hg a hp A hAa C = 0 := by
      rw [coefficient]
      apply Finset.sum_eq_zero
      intro D _
      have hD := ExpectedComponentCycle.support_subset X m p k A W D.val D.property
      have hz : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (D.val.val : Set X.carrier) := fun h => hpoint ⟨hD.1 h, hD.2 h⟩
      rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_right hz, mul_zero]
    rw [hleft, hright]

include hp hAa in
theorem intersection_mem
    (hproper : CycleClass.Thom.IntersectionGeometry.MeetProperly X p (k + 1) (Finsupp.single A 1)
      (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g)) :
    Supports.ProperCycle.intersectionBilinear X m p (k + 1) (Finsupp.single A 1)
      (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) := by
  have hi := Supports.ProperCycle.intersectionBilinear_isProper X m p (k + 1) (Finsupp.single A 1)
    (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) hproper
  have hc : Supports.ProperCycle.intersectionBilinear X m p (k + 1) (Finsupp.single A 1)
      (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) = cycle X m p k W g hg a hp A hAa := by
    ext C
    rw [hi.2 C, Finsupp.sum_single_index (by simp)]
    simp only [one_mul]
    refine Eq.trans ?_ (all_coefficients X m p k W g hg a hp A hAa C)
    apply Finset.sum_congr rfl
    intro B _
    exact congrArg (fun r : ℚ => (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) B * r)
      (Symmetry.multiplicity_comm X A.val B.val C.val)
  rw [hc]
  exact rationally_zero X m p k W g hg a hp A hAa

end Relation

end

/-! Principal descent for an arbitrary cycle meeting the actual
numerator and denominator support cover. The fixed finite descent
strata contain only that cover and the principal divisor's supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem covered (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (Principal.ChartSupportCover.family X m k W g hg))
    (hdiv : CycleClass.Thom.IntersectionGeometry.MeetProperly X p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g)) :
    Supports.ProperCycle.intersectionBilinear X m p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈
      CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) := by
  let d := Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g
  have hsingle (A : X.DimensionCycleSupport p) (hA : A ∈ a.support) :
      Supports.ProperCycle.intersectionBilinear X m p (k + 1) (Finsupp.single A 1) d ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) := by
    apply Relation.intersection_mem X m p k W g hg a hp A hA
    intro B hB E hE C hC
    have hBA : B = A := by
      simpa only [Finsupp.support_single A one_ne_zero, Finset.mem_singleton] using hB
    subst B
    exact hdiv A hA E hE C hC
  have hdecomp : a = ∑ A ∈ a.support, a A • Finsupp.single A (1 : ℚ) := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact (Finsupp.sum_single a).symm
  rw [hdecomp, map_sum, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro A hA
  rw [map_smul, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (hsingle A hA)

theorem exists_strata (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0) :
    ∃ S : Finset (IrreducibleCloseds X.carrier), ∀ (p : ℕ) (a : X.RationalDimensionCycle p),
      a ∈ Proper.SupportCycles.submodule X p (fun B : S => B.val) →
      CycleClass.Thom.IntersectionGeometry.MeetProperly X p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∧
      Supports.ProperCycle.intersectionBilinear X m p (k + 1) a (Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g) ∈
        CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (p + (k + 1)) := by
  let d := Principal.ClosedSectionCycle.principalCycle X (k + 1) W.val g
  let J := Principal.ChartSupportCover.Index X m k W g hg ⊕ d.support
  let family : J → IrreducibleCloseds X.carrier :=
    Sum.elim (Principal.ChartSupportCover.family X m k W g hg) (fun B => B.val.val)
  let S := (Set.finite_range family).toFinset
  refine ⟨S, ?_⟩
  intro p a ha
  have hpos : a ∈ Proper.SupportCycles.submodule X p family := by
    intro i
    exact ha ⟨family i, by simp only [S, Set.Finite.mem_toFinset]; exact ⟨i, rfl⟩⟩
  have hdiv : CycleClass.Thom.IntersectionGeometry.MeetProperly X p (k + 1) a d := by
    intro A hA B hB C hC
    have h := hpos (.inr ⟨B, hB⟩) A hA C hC
    change p + X.supportCodimension B.val ≤ X.supportCodimension C at h
    rwa [B.property] at h
  exact ⟨hdiv, covered X m p k W g hg a (fun i => hpos (.inl i)) hdiv⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoveredPrincipalDescent
