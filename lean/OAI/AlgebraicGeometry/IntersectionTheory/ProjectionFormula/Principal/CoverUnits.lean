import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartRestrictedCoefficient

/-! # Cover Units -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.CoverUnits

noncomputable section

/-! Properness against the actual numerator and denominator supports
already makes the rational function a unit at every expected generic
intersection point. No additional unit strata are required. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal

theorem fraction_unit {R F : Type} [CommRing R] [Field F]
    (f : R →+* F) (a b : R) (ha : IsUnit a) (hb : IsUnit b)
    (g : F) (hg : g = f a / f b) : ∃ u : R, IsUnit u ∧ f u = g := by
  obtain ⟨ua, rfl⟩ := ha
  obtain ⟨ub, rfl⟩ := hb
  refine ⟨↑(ua * ub⁻¹), ⟨_, rfl⟩, ?_⟩
  rw [hg]
  simp [div_eq_mul_inv]

theorem unit (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p k : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport k) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (hg : g ≠ 0)
    (a : X.RationalDimensionCycle p)
    (hp : a ∈ Proper.SupportCycles.submodule X p (ChartSupportCover.family X m k W g hg))
    (A : X.DimensionCycleSupport p) (hAa : A ∈ a.support)
    (D : X.DimensionCycleSupport (p + k)) (hDA : D.val ≤ A.val) (hDW : D.val ≤ W.val) :
    ∃ u : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).presheaf.stalk
      (NestedGenericRestriction.point X.carrier D.val W.val hDW),
      IsUnit u ∧ algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField u = g := by
  have hηD : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (D.val : Set X.carrier) :=
    (D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).mem
  have hηA := hDA hηD
  have hηW := hDW hηD
  obtain ⟨i, hi⟩ := Affine.ChartGerm.FiniteSupportCharts.covers X W.val (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hηW
  have hirange := hi
  rw [← (Affine.ChartGerm.FiniteSupportCharts.affine X W.val i).opensRange_fromSpec] at hirange
  obtain ⟨x, hx⟩ := hirange
  change Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x = CycleClass.Thom.IntersectionGeometry.supportPoint D.val at hx
  have hvx : (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i).asIdeal ≤ x.asIdeal := by
    apply (Affine.Prime.mem_iff (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i) (Affine.ChartGerm.FiniteSupportCharts.prime X W.val i) x).mp
    rw [Affine.ChartGerm.FiniteSupportCharts.prime_support, hx]
    exact hηW
  have hu (b : Bool) : IsUnit (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hi
      (ChartEquations.equation X W.val g hg (i, b))) :=
    (ChartRestrictedCoefficient.Function.germ_unit_congr X.carrier (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i)
      (Affine.ChartGerm.FiniteSupportCharts.chart X W.val i x) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hx
      (ChartComponentSum.mem_opens X W.val i x) hi _).mp
        (ChartComponentSum.GenericUnit.unit X m p k W g hg a hp (i, b) A hAa D x hx hηA hvx)
  let σ := Local.Principal.supportStalkMap X.carrier W.val (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hηW
  let a₀ := X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hi (ChartEquations.numerator X W.val g hg i)
  let b₀ := X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W.val i) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hi (ChartEquations.denominator X W.val g hg i)
  exact fraction_unit (algebraMap _ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).functionField) (σ a₀) (σ b₀)
    ((hu true).map σ.hom) ((hu false).map σ.hom) g
    (ChartEquations.fraction X W.val g hg i (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hηW hi).2.2

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.CoverUnits
