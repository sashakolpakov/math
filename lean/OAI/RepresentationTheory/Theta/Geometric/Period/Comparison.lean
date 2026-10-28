import OAI.RepresentationTheory.Theta.Geometric.Period.Quotient
import OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.Tangent

/-! # Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The explicit holomorphic quotient has the same kernel as the supplied
analytic fiber, so its comparison is an actual linear equivalence. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

variable {x : D.domain} (F : D.ReferenceAnalyticFiber x)

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparisonMap : Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) →ₗ[ℂ] Data.ActiveHeckeThetaData.referenceTangent (s := s) :=
  F.projection.comp D.periodSection

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparisonMap_projection (hg : D.pel.HasIntegralModelGeometry)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    F.periodComparisonMap D (D.periodProjection x.val u) = F.projection u := by
  have hk : D.periodSection (D.periodProjection x.val u) - u ∈ (D.periodProjection x.val).ker := by
    change D.periodProjection x.val (_ - _) = 0
    rw [map_sub, D.periodProjection_section hg, sub_self]
  rw [D.periodProjection_kernel hg, ← F.kernel] at hk
  change F.projection (_ - _) = 0 at hk
  rw [map_sub, sub_eq_zero] at hk
  exact hk

theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparisonMap_bijective (hg : D.pel.HasIntegralModelGeometry) :
    Function.Bijective (F.periodComparisonMap D) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    have hk : D.periodSection t ∈ F.projection.ker := ht
    rw [F.kernel, ← D.periodProjection_kernel hg] at hk
    change D.periodProjection x.val (D.periodSection t) = 0 at hk
    rwa [D.periodProjection_section hg] at hk
  · intro t
    obtain ⟨u, rfl⟩ := F.surjective t
    exact ⟨D.periodProjection x.val u, F.periodComparisonMap_projection D hg u⟩

def Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparison (hg : D.pel.HasIntegralModelGeometry) :
    Data.ActiveHeckeThetaData.PeriodQuotientCoordinates (s := s) ≃ₗ[ℂ] Data.ActiveHeckeThetaData.referenceTangent (s := s) :=
  LinearEquiv.ofBijective (F.periodComparisonMap D) (F.periodComparisonMap_bijective D hg)

@[simp] theorem Data.ActiveHeckeThetaData.ReferenceAnalyticFiber.periodComparison_projection (hg : D.pel.HasIntegralModelGeometry)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    F.periodComparison D hg (D.periodProjection x.val u) = F.projection u :=
  F.periodComparisonMap_projection D hg u

end

end OAI.RepresentationTheory.Theta.Geometric
