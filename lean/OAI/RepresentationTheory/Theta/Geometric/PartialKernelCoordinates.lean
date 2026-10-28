import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelCoordinates

/-! # Partial Kernel Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.PartialKernelCoordinates

noncomputable section

/-! A normalized kernel at one point supplies local holomorphic
coordinates for every nearby normalized vector killed by the same matrix.
No kernel condition is imposed at the other points of the neighborhood. -/

open Set

theorem exists_holomorphic_partial_kernel_coordinate
    {S W : Type} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (p : S → Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] W) (U : Set S) (hU : IsOpen U)
    (hp : DifferentiableOn ℂ p U) (q₀ : S) (hq₀ : q₀ ∈ U) (z₀ : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hz₀ : (p q₀).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z₀}) :
    ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧
      ∀ q ∈ O, ∀ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, p q (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = 0 → period q = z := by
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
  obtain ⟨O, D, hO, hqO, hOU, hD, hInv⟩ := AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential.exists_holomorphic_inverse_differential_neighborhood
    B U hU (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_nat_of_differentiableOn hU hB 2)
    q₀ hq₀ (ContinuousLinearEquiv.refl ℂ Geometry.ComplexBall.PrescribedSignsB.BallChart) hB₀
  let t := fun q => l (p q (Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)))
  let period := fun q => -(D q).symm (t q)
  have ht : DifferentiableOn ℂ t O := (differentiableOn_const l).clm_apply
    ((hp.mono hOU).clm_apply (differentiableOn_const (Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart))))
  refine ⟨O, period, hO, hqO, hOU, ((hInv.differentiableOn (by norm_num)).clm_apply ht).neg, ?_⟩
  intro q hq z hzero
  have heq : B q z + t q = 0 := by
    have he := congrArg l hzero
    rw [Normalized.KernelCoordinates.lineVector_horizontal, map_add, map_add, map_zero] at he
    exact he
  have hDz : D q z = -t q := by
    have he : D q z = B q z := congrArg (fun f : Geometry.ComplexBall.PrescribedSignsB.BallChart →L[ℂ] Geometry.ComplexBall.PrescribedSignsB.BallChart => f z) (hD q hq)
    exact he.trans (eq_neg_of_add_eq_zero_left heq)
  apply (D q).injective
  change D q (-(D q).symm (t q)) = D q z
  rw [map_neg, ContinuousLinearEquiv.apply_symm_apply, hDz]

end

end OAI.RepresentationTheory.Theta.Geometric.PartialKernelCoordinates
