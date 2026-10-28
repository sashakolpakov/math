import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelCoordinates

/-! # Kernel Line Stability -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelLineStability

noncomputable section

/-! A one-dimensional holomorphic matrix kernel remains a normalized
line near a parameter where it already has affine line coordinates. -/

open Set

theorem exists_horizontal_injective_neighborhood
    {S W : Type} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (p : S → Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] W) (U : Set S) (hU : IsOpen U) (hp : DifferentiableOn ℂ p U)
    (q₀ : S) (hq₀ : q₀ ∈ U) (z₀ : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz₀ : (p q₀).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z₀}) :
    ∃ O : Set S, IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      ∀ q ∈ O, Function.Injective ((p q).toLinearMap.comp Normalized.KernelCoordinates.horizontalLineMap) := by
  obtain ⟨l₀, hl₀⟩ := ((p q₀).toLinearMap.comp Normalized.KernelCoordinates.horizontalLineMap).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (Normalized.KernelCoordinates.normalized_kernel_horizontal_injective (p q₀).toLinearMap z₀ hz₀))
  let l := l₀.toContinuousLinearMap
  let a := Normalized.KernelCoordinates.horizontalLineMap.toContinuousLinearMap
  let B := fun q => l.comp ((p q).comp a)
  have hB : DifferentiableOn ℂ B U := (differentiableOn_const l).clm_comp
    (hp.clm_comp (differentiableOn_const a))
  have hB₀ : B q₀ = (ContinuousLinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hl₀ v
  obtain ⟨O, D, hO, hqO, hOU, hD, _⟩ := AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential.exists_holomorphic_inverse_differential_neighborhood
    B U hU (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_nat_of_differentiableOn hU hB 2)
    q₀ hq₀ (ContinuousLinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart) hB₀
  refine ⟨O, hO, hqO, hOU, ?_⟩
  intro q hq v w hvw
  apply (D q).injective
  have hv := congrArg (fun d : Geometry.ComplexBall.PrescribedSignsB.BallChart →L[ℂ] Geometry.ComplexBall.PrescribedSignsB.BallChart => d v) (hD q hq)
  have hw := congrArg (fun d : Geometry.ComplexBall.PrescribedSignsB.BallChart →L[ℂ] Geometry.ComplexBall.PrescribedSignsB.BallChart => d w) (hD q hq)
  exact hv.trans ((congrArg l hvw).trans hw.symm)

theorem exists_holomorphic_kernel_line_of_finrank_one
    {S W : Type} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (p : S → Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] W) (U : Set S) (hU : IsOpen U) (hp : DifferentiableOn ℂ p U)
    (q₀ : S) (hq₀ : q₀ ∈ U) (z₀ : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz₀ : (p q₀).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z₀})
    (hdim : ∀ q ∈ U, Module.finrank ℂ (p q).ker = 1) :
    ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧
      ∀ q ∈ O, (p q).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period q)} := by
  obtain ⟨V, hV, hqV, hVU, hi⟩ := exists_horizontal_injective_neighborhood p U hU hp q₀ hq₀ z₀ hz₀
  obtain ⟨O, period, hO, hqO, hOV, hhol, hk⟩ := Normalized.KernelCoordinates.exists_holomorphic_normalized_kernel_coordinate
    p V hV (hp.mono hVU) q₀ hqV
    (fun q hq => (Normalized.KernelCoordinates.exists_normalized_kernel_of_horizontal_injective (p q).toLinearMap
      (hdim q (hVU hq)) (hi q hq)).exists)
  exact ⟨O, period, hO, hqO, hOV.trans hVU, hhol, hk⟩

end

end OAI.RepresentationTheory.Theta.Geometric.KernelLineStability
