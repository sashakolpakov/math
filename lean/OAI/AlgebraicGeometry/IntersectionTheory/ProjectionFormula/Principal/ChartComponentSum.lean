import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalComponentSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm

/-! # Chart Component Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartComponentSum

noncomputable section

section

/-! The original principal-divisor pairing is a finite sum over the
fixed ambient intersection components, weighted by the difference of
the actual numerator and denominator germ orders. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem mem_opens (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i)) : Affine.ChartGerm.FiniteSupportCharts.chart X W i x ∈ Affine.ChartGerm.FiniteSupportCharts.opens X W i := by
  rw [← (Affine.ChartGerm.FiniteSupportCharts.affine X W i).opensRange_fromSpec]
  exact ⟨x, rfl⟩

def germ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1)) :
    X.carrier.presheaf.stalk (Affine.ChartGerm.FiniteSupportCharts.chart X W i.1 x) :=
  X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i.1) (Affine.ChartGerm.FiniteSupportCharts.chart X W i.1 x) (mem_opens X W i.1 x)
    (ChartEquations.equation X W g hg i)

theorem germ_map (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1)) :
    (Affine.ChartGerm.FiniteSupportCharts.chart X W i.1).stalkMap x (ChartComponentSum.germ X W g hg i x) =
      StructureSheaf.toStalk (Affine.ChartGerm.FiniteSupportCharts.ring X W i.1) x (ChartEquations.equation X W g hg i) :=
  Affine.ChartGerm.apply X.carrier (Affine.ChartGerm.FiniteSupportCharts.opens X W i.1) (Affine.ChartGerm.FiniteSupportCharts.affine X W i.1) x
    (mem_opens X W i.1 x) (ChartEquations.equation X W g hg i)

theorem equation (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal ≤ x.asIdeal) :
    CoveredPrincipalExpansion.pairing (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1)
      (ChartEquations.equation X W.val g hg i) A₀ x hxA hvx m =
      ∑ D ∈ Finite.ClosedComponents.components X.carrier
          (IsolatedGeometricComponents.intersection X.carrier W.val A.val),
        TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
          GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 x) (ChartComponentSum.germ X W.val g hg i x) D := by
  apply Affine.PrincipalComponentSum.coefficient X m p (k + 1) (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)
    (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1) (ChartEquations.equation X W.val g hg i)
    (ChartEquations.equation_avoid X W.val g hg i) W.val (Affine.ChartGerm.FiniteSupportCharts.prime_point X W.val i.1)
    (ChartSupportCover.supports X m k W g hg i)
    (ChartSupportCover.codimension X m k W g hg i)
    (ChartSupportCover.covers X m k W g hg i) A A₀ hA ?_ C x hx hxA hvx
    (ChartComponentSum.germ X W.val g hg i x) (germ_map X W.val g hg i x)
  intro B hB
  exact hp ⟨i, ⟨B, hB⟩⟩ A hAa

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (F : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool, Finset (PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)))
    (hF : DescentPosition.PrimeData X k W.val g hg F)
    (hout : DescentPosition.Outside X k W.val g hg F)
    (a : X.RationalDimensionCycle p)
    (he : DescentPosition.Expansions X p k W.val g hg F a)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (A₀ : IrreducibleCloseds (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))))
    (hA : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i (CycleClass.Thom.IntersectionGeometry.supportPoint A₀) = CycleClass.Thom.IntersectionGeometry.supportPoint A.val)
    (C : X.DimensionCycleSupport (p + (k + 1))) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : x ∈ (A₀ : Set (Spec (.of (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i)))))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal) :
    (ClosedSectionCycle.principalCycle X (k + 1) W.val g).sum
      (fun B c => c * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B.val A.val C.val) =
      ∑ D ∈ Finite.ClosedComponents.components X.carrier
          (IsolatedGeometricComponents.intersection X.carrier W.val A.val),
        TotalTorCoefficient.coefficient X.carrier W.val A.val (CycleClass.Thom.IntersectionGeometry.supportPoint D) m *
          (GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) (ChartComponentSum.germ X W.val g hg (i, true) x) D -
            GlobalParameterSum.Weights.weight X.carrier (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) (ChartComponentSum.germ X W.val g hg (i, false) x) D) := by
  refine (ChartEuler.coefficient X m p k W g hg F hF hout a he hp i A hAa A₀ hA C x hx hxA hvx).trans ?_
  refine (congrArg₂ (fun a b : ℚ => a - b)
    (equation X m p k W g hg a hp (i, true) A hAa A₀ hA C x hx hxA hvx)
    (equation X m p k W g hg a hp (i, false) A hAa A₀ hA C x hx hxA hvx)).trans ?_
  simp only [mul_sub, Finset.sum_sub_distrib]

end

/-! Properness against the full numerator and denominator zero loci
makes both chart equations units at generic intersection points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace GenericUnit

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem toStalk_unit (R : Type) [CommRing R] (x : PrimeSpectrum R) (r : R) (hr : r ∉ x.asIdeal) :
    IsUnit (StructureSheaf.toStalk R x r) := by
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime x.asIdeal) x.asIdeal r).mpr hr
  have h := hu.map (StructureSheaf.stalkIso R x).toRingHom
  change IsUnit ((StructureSheaf.stalkIso R x) (algebraMap R (Localization.AtPrime x.asIdeal) r)) at h
  rwa [(StructureSheaf.stalkIso R x).commutes] at h

theorem not_mem (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (C : X.DimensionCycleSupport (p + k)) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal ≤ x.asIdeal) :
    ChartEquations.equation X W.val g hg i ∉ x.asIdeal := by
  have hn := Affine.ModuleSupportCover.avoids X p k (k + 1) (Nat.lt_succ_self k)
    (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1) (ChartSupportCover.module X k W g hg i)
    (ChartSupportCover.supports X m k W g hg i)
    (ChartSupportCover.codimension X m k W g hg i)
    (ChartSupportCover.covers X m k W g hg i) A
    (fun B hB => hp ⟨i, ⟨B, hB⟩⟩ A hAa) C x hx hxA
  intro hr
  apply hn
  change x ∈ Module.support (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1)
    (QuotSMulTop (ChartEquations.equation X W.val g hg i) ((Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) ⧸ (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal))
  rw [Module.support_quotSMulTop, Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  exact ⟨hvx, Set.singleton_subset_iff.mpr hr⟩

theorem unit (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W.val × Bool) (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (C : X.DimensionCycleSupport (p + k)) (x : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1))
    (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1 x = CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (hxA : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i.1).asIdeal ≤ x.asIdeal) :
    IsUnit (ChartComponentSum.germ X W.val g hg i x) := by
  apply isUnit_of_map_unit ((Affine.ChartGerm.FiniteSupportCharts.chart X W.val i.1).stalkMap x).hom
  rw [germ_map]
  exact toStalk_unit (Affine.ChartGerm.FiniteSupportCharts.ring X W.val i.1) x (ChartEquations.equation X W.val g hg i)
    (not_mem X m p k W g hg a hp i A hAa C x hx hxA hvx)

end GenericUnit

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartComponentSum
