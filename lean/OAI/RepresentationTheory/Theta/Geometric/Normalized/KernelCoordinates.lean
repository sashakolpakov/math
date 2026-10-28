import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine
import OAI.AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF

/-! # Kernel Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelCoordinates

noncomputable section

section

/-! A holomorphic matrix whose kernel is a normalized line determines
that line's two affine coordinates holomorphically near every point. -/

open Set

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

def horizontalLineMap : Geometry.ComplexBall.PrescribedSignsB.BallChart →ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec where
  toFun v := ![v 0, v 1, 0]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' a v := by ext i; fin_cases i <;> simp

theorem lineVector_horizontal (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Geometry.ComplexBall.PrescribedSignsB.lineVector z = horizontalLineMap z + Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart) := by
  ext i
  fin_cases i <;> simp [horizontalLineMap, Geometry.ComplexBall.PrescribedSignsB.lineVector]

theorem horizontalLineMap_injective : Function.Injective horizontalLineMap := by
  intro v w h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

theorem normalized_kernel_horizontal_injective
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (p : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] W) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (hp : p.ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) :
    Function.Injective (p.comp horizontalLineMap) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hvp : horizontalLineMap v ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} := hp ▸ hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hvp
  have ha0 : a = 0 := by simpa [horizontalLineMap, Geometry.ComplexBall.PrescribedSignsB.lineVector] using congrFun ha 2
  rw [ha0, zero_smul] at ha
  exact horizontalLineMap_injective (ha.symm.trans horizontalLineMap.map_zero.symm)

theorem exists_holomorphic_normalized_kernel_coordinate
    {S W : Type} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (p : S → Geometry.ComplexBall.PrescribedSignsB.Vec →L[ℂ] W) (U : Set S) (hU : IsOpen U)
    (hp : DifferentiableOn ℂ p U) (q₀ : S) (hq₀ : q₀ ∈ U)
    (hline : ∀ q ∈ U, ∃ z : Geometry.ComplexBall.PrescribedSignsB.BallChart, (p q).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z}) :
    ∃ (O : Set S) (period : S → Geometry.ComplexBall.PrescribedSignsB.BallChart), IsOpen O ∧ q₀ ∈ O ∧ O ⊆ U ∧
      DifferentiableOn ℂ period O ∧
      ∀ q ∈ O, (p q).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period q)} := by
  obtain ⟨z₀, hz₀⟩ := hline q₀ hq₀
  obtain ⟨l₀, hl₀⟩ := ((p q₀).toLinearMap.comp horizontalLineMap).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (normalized_kernel_horizontal_injective (p q₀).toLinearMap z₀ hz₀))
  let l := l₀.toContinuousLinearMap
  let a := horizontalLineMap.toContinuousLinearMap
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
  intro q hq
  obtain ⟨z, hz⟩ := hline q (hOU hq)
  have hzero : p q (Geometry.ComplexBall.PrescribedSignsB.lineVector z) = 0 := by
    change Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ (p q).ker
    rw [hz]
    exact Submodule.mem_span_singleton_self (Geometry.ComplexBall.PrescribedSignsB.lineVector z)
  have heq : B q z + t q = 0 := by
    have he := congrArg l hzero
    rw [lineVector_horizontal, map_add, map_add, map_zero] at he
    exact he
  have hDz : D q z = -t q := by
    have he : D q z = B q z := congrArg (fun f : Geometry.ComplexBall.PrescribedSignsB.BallChart →L[ℂ] Geometry.ComplexBall.PrescribedSignsB.BallChart => f z) (hD q hq)
    exact he.trans (eq_neg_of_add_eq_zero_left heq)
  have hcoord : period q = z := by
    apply (D q).injective
    change D q (-(D q).symm (t q)) = D q z
    rw [map_neg, ContinuousLinearEquiv.apply_symm_apply, hDz]
  exact hz.trans (congrArg (fun w => Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector w}) hcoord.symm)

end

/-! A one-dimensional kernel transverse to the horizontal plane has
a unique normalized affine line coordinate. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine

theorem exists_unique_normalized_line_of_last_injective (P : Submodule ℂ Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hdim : Module.finrank ℂ P = 1) (hP : ∀ v ∈ P, v 2 = 0 → v = 0) :
    ∃! z : Geometry.ComplexBall.PrescribedSignsB.BallChart, P = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (hdim ▸ Nat.zero_lt_one)
  have hnv : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  have hlast : v.val 2 ≠ 0 := fun h => hnv (hP v.val v.property h)
  let z := AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine.negativeLineCoordinate v.val
  have hz : Geometry.ComplexBall.PrescribedSignsB.lineVector z ∈ P := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine.negativeLineCoordinate_vector v.val hlast).symm ▸
    P.smul_mem (v.val 2)⁻¹ v.property
  have hspan : Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} = P :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hz))
      ((finrank_span_singleton (Geometry.ComplexBall.PrescribedSignsB.lineVector_ne_zero z)).trans hdim.symm)
  exact ⟨z, hspan.symm, fun w hw => AlgebraicGeometry.AbelianModuli.ReferenceFamily.NegativeLine.lineVector_span_injective (hw.symm.trans hspan.symm)⟩

theorem kernel_last_injective_of_horizontal_injective
    {W : Type} [AddCommGroup W] [Module ℂ W] (p : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] W)
    (hi : Function.Injective (p.comp horizontalLineMap)) :
    ∀ v ∈ p.ker, v 2 = 0 → v = 0 := by
  intro v hv hv2
  let w : Geometry.ComplexBall.PrescribedSignsB.BallChart := ![v 0, v 1]
  have hw : horizontalLineMap w = v := by
    ext i
    fin_cases i <;> simp [horizontalLineMap, w, hv2]
  have hw0 : w = 0 := hi (by
    change p (horizontalLineMap w) = p (horizontalLineMap 0)
    rw [hw, map_zero, map_zero]
    exact hv)
  exact hw.symm.trans ((congrArg horizontalLineMap hw0).trans horizontalLineMap.map_zero)

theorem exists_normalized_kernel_of_horizontal_injective
    {W : Type} [AddCommGroup W] [Module ℂ W] (p : Geometry.ComplexBall.PrescribedSignsB.Vec →ₗ[ℂ] W)
    (hdim : Module.finrank ℂ p.ker = 1)
    (hi : Function.Injective (p.comp horizontalLineMap)) :
    ∃! z : Geometry.ComplexBall.PrescribedSignsB.BallChart, p.ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector z} :=
  exists_unique_normalized_line_of_last_injective p.ker hdim
    (kernel_last_injective_of_horizontal_injective p hi)

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelCoordinates
