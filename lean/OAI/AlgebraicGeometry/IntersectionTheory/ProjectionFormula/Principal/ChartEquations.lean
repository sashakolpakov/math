import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm

/-! # Chart Equations -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

noncomputable section

/-! Fixed numerator and denominator sections for a nonzero support
rational function, chosen on the finite ambient affine chart cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : TopologicalSpace.IrreducibleCloseds X.carrier)
  (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)

def numerator : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W, Affine.ChartGerm.FiniteSupportCharts.ring X W i := (Affine.ChartGerm.FiniteSupportCharts.exists_fractions X W g hg).choose

def denominator : ∀ i : Affine.ChartGerm.FiniteSupportCharts.Index X W, Affine.ChartGerm.FiniteSupportCharts.ring X W i := (Affine.ChartGerm.FiniteSupportCharts.exists_fractions X W g hg).choose_spec.choose

theorem avoid (i : Affine.ChartGerm.FiniteSupportCharts.Index X W) :
    numerator X W g hg i ∉ (Affine.ChartGerm.FiniteSupportCharts.prime X W i).asIdeal ∧
      denominator X W g hg i ∉ (Affine.ChartGerm.FiniteSupportCharts.prime X W i).asIdeal :=
  (Affine.ChartGerm.FiniteSupportCharts.exists_fractions X W g hg).choose_spec.choose_spec.1 i

def equation (i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool) : Affine.ChartGerm.FiniteSupportCharts.ring X W i.1 :=
  if i.2 then numerator X W g hg i.1 else denominator X W g hg i.1

theorem equation_avoid (i : Affine.ChartGerm.FiniteSupportCharts.Index X W × Bool) : equation X W g hg i ∉ (Affine.ChartGerm.FiniteSupportCharts.prime X W i.1).asIdeal := by
  cases h : i.2 <;> simp only [equation, h, Bool.false_eq_true, ↓reduceIte]
  · exact (avoid X W g hg i.1).2
  · exact (avoid X W g hg i.1).1

theorem fraction (i : Affine.ChartGerm.FiniteSupportCharts.Index X W) (x : X.carrier) (hxW : x ∈ (W : Set X.carrier)) (hxU : x ∈ Affine.ChartGerm.FiniteSupportCharts.opens X W i) :
    Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
      (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) x hxU (numerator X W g hg i)) ≠ 0 ∧
    Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
      (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) x hxU (denominator X W g hg i)) ≠ 0 ∧
    g = Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
      (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) x hxU (numerator X W g hg i)) /
      Support.LocalFraction.Restriction.toFunctionField X.carrier W x hxW
        (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) x hxU (denominator X W g hg i)) :=
  (Affine.ChartGerm.FiniteSupportCharts.exists_fractions X W g hg).choose_spec.choose_spec.2 i x hxW hxU

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations
