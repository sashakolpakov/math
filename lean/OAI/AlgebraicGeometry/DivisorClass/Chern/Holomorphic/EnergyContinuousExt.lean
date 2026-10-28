import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.OneEnergy
import OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCutoffGlobal
import OAI.AlgebraicGeometry.DivisorClass.Chern.EnergyCoercivity

/-! # Energy Continuous Ext -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyContinuousExt

noncomputable section

section

/-! The actual closure of original smooth forms inside the native joint energy Hilbert space. -/

open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

local instance smoothCore_fullNormedSpace : NormedSpace ℂ (HolomorphicMetric.OneEnergy.HolomorphicOneEnergyWith V h) :=
  Submodule.normedSpace (𝕜 := ℂ) (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySubmodule V h)

local instance smoothCore_fullInnerProductSpace : InnerProductSpace ℂ (HolomorphicMetric.OneEnergy.HolomorphicOneEnergyWith V h) :=
  Submodule.innerProductSpace (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySubmodule V h)

def holomorphicMetricSmoothEnergySubmodule : Submodule ℂ (HolomorphicMetric.OneEnergy.HolomorphicOneEnergyWith V h) :=
  (LinearMap.range (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h)).topologicalClosure

abbrev HolomorphicSmoothOneEnergyWith := holomorphicMetricSmoothEnergySubmodule V h

local instance smoothCore_normedSpace : NormedSpace ℂ (HolomorphicSmoothOneEnergyWith V h) :=
  Submodule.normedSpace (𝕜 := ℂ) (holomorphicMetricSmoothEnergySubmodule V h)

local instance smoothCore_innerProductSpace : InnerProductSpace ℂ (HolomorphicSmoothOneEnergyWith V h) :=
  Submodule.innerProductSpace (holomorphicMetricSmoothEnergySubmodule V h)

instance holomorphicMetricSmoothEnergy_completeSpace : CompleteSpace (HolomorphicSmoothOneEnergyWith V h) :=
  (LinearMap.range (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h)).isClosed_topologicalClosure.completeSpace_coe

def holomorphicMetricSmoothEnergyInclusion :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] HolomorphicSmoothOneEnergyWith V h :=
  (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h).codRestrict _ (fun a =>
    (LinearMap.range (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h)).le_topologicalClosure ⟨a, rfl⟩)

def holomorphicMetricSmoothEnergySource : HolomorphicSmoothOneEnergyWith V h →L[ℂ] AntiOneSourcePair.HolomorphicAntiOneL2With V h :=
  (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySource V h).comp (holomorphicMetricSmoothEnergySubmodule V h).subtypeL

/-- The smooth inclusion has the original antiholomorphic source. -/
def HolomorphicSmoothEnergySourceCompatible : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    holomorphicMetricSmoothEnergySource V h (holomorphicMetricSmoothEnergyInclusion V h a) =
      AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a

/-- Original smooth forms are dense in the smooth energy completion. -/
def HolomorphicSmoothEnergyInclusionDense : Prop :=
  DenseRange (holomorphicMetricSmoothEnergyInclusion V h)

theorem holomorphicMetricSmoothEnergyInclusion_source :
    HolomorphicSmoothEnergySourceCompatible V h := by
  intro a
  rfl

theorem holomorphicMetricSmoothEnergyInclusion_dense :
    HolomorphicSmoothEnergyInclusionDense V h :=
  EnergyCoercivity.linearRangeClosure_inclusion_dense (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h)

end

/-! Continuous functions on the actual smooth energy closure are determined by their values on original smooth forms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] smoothCore_fullNormedSpace smoothCore_fullInnerProductSpace
  smoothCore_normedSpace smoothCore_innerProductSpace

theorem holomorphicMetricSmoothEnergy_continuous_ext (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    {G : Type*} [TopologicalSpace G] [T2Space G]
    (P Q : HolomorphicSmoothOneEnergyWith V h → G) (hP : Continuous P) (hQ : Continuous Q)
    (hPQ : ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
      P (holomorphicMetricSmoothEnergyInclusion V h a) = Q (holomorphicMetricSmoothEnergyInclusion V h a))
    (v : HolomorphicSmoothOneEnergyWith V h) : P v = Q v :=
  congrFun ((holomorphicMetricSmoothEnergyInclusion_dense V h).equalizer hP hQ (funext hPQ)) v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyContinuousExt
