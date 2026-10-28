import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cover

/-! # Quotient Sheets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuotientSheets.CM

noncomputable section

/-! Construct holomorphic local sheets of the native quotient projections
and of their descended maps. No local-diffeomorphism premise is supplied
for the quotient map being constructed. -/

open scoped _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverDerivative.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth.CM

section Analytic

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [FiniteDimensional ℂ W]
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace V X] [ChartedSpace W Y]
  [IsManifold 𝓘(ℂ, V) 1 X] [IsManifold 𝓘(ℂ, W) 1 Y]

theorem local_diffeomorph_of_holomorphic_cover
    (eV : V ≃L[ℂ] HeckeCycles.GeometricSource.CM.BallChart) (eW : W ≃L[ℂ] HeckeCycles.GeometricSource.CM.BallChart)
    (f : X → Y) (hcover : IsCoveringMap f)
    (hf : MDifferentiable 𝓘(ℂ, V) 𝓘(ℂ, W) f)
    (hbij : ∀ x, Function.Bijective (mfderiv 𝓘(ℂ, V) 𝓘(ℂ, W) f x)) :
    IsLocalDiffeomorph 𝓘(ℂ, V) 𝓘(ℂ, W) 1 f := by
  intro x
  obtain ⟨e, hx, he⟩ := hcover.isLocalHomeomorph x
  have hinv : MDifferentiable 𝓘(ℂ, W) 𝓘(ℂ, V)
      (fun y : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens Y) => e.symm y) := by
    intro y
    have hi := HeckeCycles.CoverDerivative.CM.mdifferentiableAt_local_inverse e (e.map_target y.property)
      (he ▸ hf (e.symm y)) (he ▸ hbij (e.symm y))
    rw [e.right_inv y.property] at hi
    exact hi.comp y ((contMDiff_subtype_val (I := 𝓘(ℂ, W)) (n := 1)).mdifferentiable one_ne_zero y)
  have hs := HeckeCycles.CoverSmooth.CM.contMDiff_of_model_equiv eV hf
  have his := HeckeCycles.CoverSmooth.CM.contMDiff_of_model_equiv eW hinv
  let φ : PartialDiffeomorph 𝓘(ℂ, V) 𝓘(ℂ, W) X Y 1 :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℂ, V) 𝓘(ℂ, W) 1 (e : X → Y) e.source
        rw [← he]
        exact (hs.of_le (by simp)).contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        exact ((contMDiffAt_subtype_iff.mp (his ⟨y, hy⟩)).of_le (by simp)).contMDiffWithinAt }
  exact ⟨φ, hx, fun y _ => congrFun he y⟩

end Analytic

section Descent

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {D X Y : Type*} [TopologicalSpace D] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace U D] [ChartedSpace V X] [ChartedSpace W Y]

theorem descended_local_diffeomorph
    (π : D → X) (ρ : D → Y) (hπ : Function.Surjective π)
    (hπlocal : IsLocalDiffeomorph 𝓘(ℂ, U) 𝓘(ℂ, V) 1 π)
    (hρlocal : IsLocalDiffeomorph 𝓘(ℂ, U) 𝓘(ℂ, W) 1 ρ)
    (f : X → Y) (hcomp : ∀ z, f (π z) = ρ z) :
    IsLocalDiffeomorph 𝓘(ℂ, V) 𝓘(ℂ, W) 1 f := by
  intro x
  obtain ⟨z, rfl⟩ := hπ x
  obtain ⟨a, ha, hpa⟩ := hπlocal z
  obtain ⟨b, hb, hpb⟩ := hρlocal z
  have hta : π z ∈ a.target := hpa ha ▸ a.map_source ha
  have hia : a.invFun (π z) = z := by rw [hpa ha]; exact a.left_inv ha
  refine ⟨a.symm.trans b, ⟨hta, ?_⟩, ?_⟩
  · change a.invFun (π z) ∈ b.source
    rw [hia]
    exact hb
  · intro y hy
    change f y = b (a.invFun y)
    have hsource := a.map_target hy.1
    have hright : π (a.invFun y) = y := (hpa hsource).trans (a.right_inv hy.1)
    calc
      f y = f (π (a.invFun y)) := congrArg f hright.symm
      _ = ρ (a.invFun y) := hcomp _
      _ = b (a.invFun y) := hpb hy.2

end Descent

variable {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]

theorem principal_projection_local_diffeomorph
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (S : Cm.PrincipalBallSurface K B N) :
    IsLocalDiffeomorph 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, S.surface.variety.analyticModel) 1 S.projection := by
  let z := HeckeCycles.CoverSmooth.CM.ballBasePoint B
  let D : HeckeCycles.GeometricSource.CM.BallChart →L[ℂ] S.surface.variety.analyticModel :=
    mfderiv 𝓘(ℂ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℂ, S.surface.variety.analyticModel) S.projection z
  let L : HeckeCycles.GeometricSource.CM.BallChart ≃L[ℂ] S.surface.variety.analyticModel :=
    (LinearEquiv.ofBijective D.toLinearMap
      (S.isBallCover.2.2.2.2.1 z)).toContinuousLinearEquiv
  exact local_diffeomorph_of_holomorphic_cover (ContinuousLinearEquiv.refl ℂ HeckeCycles.GeometricSource.CM.BallChart) L.symm
    S.projection S.isBallCover.2.2.1 S.isBallCover.2.2.2.1 S.isBallCover.2.2.2.2.1

theorem principal_map_local_diffeomorph
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N M : ℕ)
    (S : Cm.PrincipalBallSurface K B N) (T : Cm.PrincipalBallSurface K B M)
    (f : T.surface.variety.analyticSpace → S.surface.variety.analyticSpace)
    (hover : ∀ z : B.Domain, f (T.projection z) = S.projection z) :
    IsLocalDiffeomorph 𝓘(ℂ, T.surface.variety.analyticModel)
      𝓘(ℂ, S.surface.variety.analyticModel) 1 f :=
  descended_local_diffeomorph T.projection S.projection T.isBallCover.2.1
    (principal_projection_local_diffeomorph B M T)
    (principal_projection_local_diffeomorph B N S) f hover

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuotientSheets.CM
