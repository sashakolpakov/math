import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CriticalImage
import OAI.RepresentationTheory.Theta.Geometric.ContinuousAnalyticRemovable
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! # Homeomorph Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.HomeomorphInverse

noncomputable section

/-! An open partial homeomorphism in complex coordinates has a holomorphic
inverse when its forward map is holomorphic. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter _root_.Metric
open scoped _root_.Topology

variable {n : ℕ} (q : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))

theorem holomorphic_homeomorph_inverse_regular (hq : DifferentiableOn ℂ q q.source)
    {y : Fin n → ℂ} (hy : y ∈ q.target) (hj : Jacobian.holomorphicJacobian q (q.symm y) ≠ 0) :
    DifferentiableAt ℂ q.symm y := by
  have hi := (Jacobian.holomorphicJacobian_ne_zero_iff (f := q) (q.symm y)).mp hj
  have hb : Function.Bijective (fderiv ℂ q (q.symm y)) :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  let e := (LinearEquiv.ofBijective (fderiv ℂ q (q.symm y)).toLinearMap hb).toContinuousLinearEquiv
  have hd : HasFDerivAt q e.toContinuousLinearMap (q.symm y) :=
    (hq.differentiableAt (q.open_source.mem_nhds (q.map_target hy))).hasFDerivAt
  exact (q.hasFDerivAt_symm hy hd).differentiableAt

theorem holomorphic_homeomorph_inverse (hq : DifferentiableOn ℂ q q.source) :
    DifferentiableOn ℂ q.symm q.target := by
  intro y hy
  let x := q.symm y
  have hx : x ∈ q.source := q.map_target hy
  obtain ⟨r, hr, hKU⟩ := nhds_basis_closedBall.mem_iff.mp (q.open_source.mem_nhds hx)
  let K := closedBall x r
  let S := q '' CriticalImage.holomorphicCriticalPiece q K
  have hxK : x ∈ K := mem_closedBall_self hr.le
  have hK : K ∈ 𝓝 x := closedBall_mem_nhds x hr
  have hlocal : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt S y := by
    have h := CriticalImage.holomorphicCriticalImage_local q.open_source hq q.injOn (isCompact_closedBall x r) hKU hxK hK
    simpa only [x, q.right_inv hy] using h
  have hn : S ∉ 𝓝 y := by
    have h := CriticalImage.holomorphicCriticalImage_not_mem_nhds q.open_source hq q.injOn hKU hx
    simpa only [x, q.right_inv hy] using h
  let V := q.target ∩ q.symm ⁻¹' interior K
  have hV : IsOpen V := q.isOpen_inter_preimage_symm isOpen_interior
  have hyV : y ∈ V := ⟨hy, mem_interior_iff_mem_nhds.mpr hK⟩
  have hd (z : Fin n → ℂ) (hz : z ∈ V) (hzS : z ∉ S) : DifferentiableAt ℂ q.symm z := by
    apply holomorphic_homeomorph_inverse_regular q hq hz.1
    intro hj
    apply hzS
    exact ⟨q.symm z, ⟨interior_subset hz.2, hj⟩, q.right_inv hz.1⟩
  have hwhole : DifferentiableAt ℂ q.symm y := by
    apply differentiableAt_pi.mpr
    intro i
    apply ContinuousAnalyticRemovable.continuous_differentiableAt_of_analytic_exception hV
      ((continuous_apply i).comp_continuousOn (q.continuousOn_symm.mono inter_subset_left))
      (fun z hz hzS => (ContinuousLinearMap.proj i).differentiableAt.comp z (hd z hz hzS))
      hyV hlocal hn
  exact hwhole.differentiableWithinAt

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.HomeomorphInverse
