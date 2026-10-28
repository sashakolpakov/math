import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalWeightTransport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.WeightDifference

/-! # Chart Coefficient -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartCoefficient

noncomputable section

/-! The original principal-divisor coefficient is exactly the
difference of the fixed affine numerator and denominator weights. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.ChartGerm.FiniteSupportCharts OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartEquations

theorem coefficient (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : IrreducibleCloseds X.carrier)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0)
    (i : Affine.ChartGerm.FiniteSupportCharts.Index X W) (z : PrimeSpectrum (Affine.ChartGerm.FiniteSupportCharts.ring X W i))
    (hvz : (Affine.ChartGerm.FiniteSupportCharts.prime X W i).asIdeal ≤ z.asIdeal)
    (C : IrreducibleCloseds X.carrier) (hx : Affine.ChartGerm.FiniteSupportCharts.chart X W i z = CycleClass.Thom.IntersectionGeometry.supportPoint C) :
    CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W g C =
      Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W i) (Affine.ChartGerm.FiniteSupportCharts.prime X W i) (ChartEquations.numerator X W g hg i) z -
      Affine.PrincipalWeight.weight (Affine.ChartGerm.FiniteSupportCharts.ring X W i) (Affine.ChartGerm.FiniteSupportCharts.prime X W i) (ChartEquations.denominator X W g hg i) z := by
  have hzU : Affine.ChartGerm.FiniteSupportCharts.chart X W i z ∈ Affine.ChartGerm.FiniteSupportCharts.opens X W i := by
    rw [← (Affine.ChartGerm.FiniteSupportCharts.affine X W i).opensRange_fromSpec]
    exact ⟨z, rfl⟩
  have hzW : Affine.ChartGerm.FiniteSupportCharts.chart X W i z ∈ (W : Set X.carrier) := by
    have h := (Affine.Prime.mem_iff (Affine.ChartGerm.FiniteSupportCharts.chart X W i) (Affine.ChartGerm.FiniteSupportCharts.prime X W i) z).mpr hvz
    exact (congrArg (fun B : IrreducibleCloseds X.carrier => Affine.ChartGerm.FiniteSupportCharts.chart X W i z ∈ (B : Set X.carrier))
      (Affine.ChartGerm.FiniteSupportCharts.prime_support X W i)).mp h
  have hfrac := ChartEquations.fraction X W g hg i (Affine.ChartGerm.FiniteSupportCharts.chart X W i z) hzW hzU
  have he := WeightDifference.order X.carrier W (Affine.ChartGerm.FiniteSupportCharts.chart X W i z) hzW
    (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) (Affine.ChartGerm.FiniteSupportCharts.chart X W i z) hzU (ChartEquations.numerator X W g hg i))
    (X.carrier.presheaf.germ (Affine.ChartGerm.FiniteSupportCharts.opens X W i) (Affine.ChartGerm.FiniteSupportCharts.chart X W i z) hzU (ChartEquations.denominator X W g hg i))
    hfrac.1 hfrac.2.1 g hfrac.2.2
  let : IsNoetherianRing Γ(X.carrier, Affine.ChartGerm.FiniteSupportCharts.opens X W i) :=
    IsLocallyNoetherian.component_noetherian ⟨Affine.ChartGerm.FiniteSupportCharts.opens X W i, Affine.ChartGerm.FiniteSupportCharts.affine X W i⟩
  have ha := Affine.PrincipalWeightTransport.chart X.carrier W (Affine.ChartGerm.FiniteSupportCharts.opens X W i) (Affine.ChartGerm.FiniteSupportCharts.affine X W i)
    z hvz hzU (ChartEquations.numerator X W g hg i)
  have hb := Affine.PrincipalWeightTransport.chart X.carrier W (Affine.ChartGerm.FiniteSupportCharts.opens X W i) (Affine.ChartGerm.FiniteSupportCharts.affine X W i)
    z hvz hzU (ChartEquations.denominator X W g hg i)
  have hcoef : CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient X W g C =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g (CycleClass.Thom.IntersectionGeometry.supportPreimage W (Affine.ChartGerm.FiniteSupportCharts.chart X W i z) hzW) : ℚ) := by
    have hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (W : Set X.carrier) :=
      (congrArg (fun x : X.carrier => x ∈ (W : Set X.carrier)) hx).mp hzW
    rw [CycleClass.Thom.IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hxW]
    apply congrArg (fun y => ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g y : ℚ))
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective
    rw [CycleClass.Thom.IntersectionGeometry.supportPreimage_spec, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]
    exact hx.symm
  exact hcoef.trans (he.symm.trans (congrArg₂ (fun a b : ℚ => a - b) ha hb).symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ChartCoefficient
