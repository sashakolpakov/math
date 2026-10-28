import OAI.Analysis.PDE.Dirichlet.LatticeCellGeometry
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel

open Set Module InnerProductSpace
open scoped ContDiff Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Variational OAI.Analysis.PDE.Weak OAI.Analysis.Calculus.Quaternion

variable {m n : ℕ} {P V ι κ : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype ι] [Fintype κ] [Nonempty κ]

omit [FiniteDimensional ℝ P] in
/-- A genuine smooth solution of the physical Moore linearization on an
arbitrary periodic lattice domain. The weak equation is constructed in
adapted coordinates and then transported back, including the flux and
gradient transformations. -/
theorem exists_smooth_moore_dirichlet_solution_of_elliptic
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (c : Basis κ ℝ V) (d : Fin (m + 1) ≃ ι ⊕ κ)
    {C : Set V} (hC : IsCompact C)
    {r ψ g : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ ∞ ψ) (hψp : LatticePeriodic e lat ψ)
    (hg : ContDiff ℝ ∞ g) (hgp : LatticePeriodic e lat g)
    (hA : ContDiff ℝ ∞ (fun x ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
      (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x))))
    {U : Set (CoordinateSpace n 4)} (hU : IsOpen U)
    (hDU : {x | r x ≤ 0} ⊆ U) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ U, ∀ z : CoordinateSpace n 4, lam * ‖z‖ ^ 2 ≤
      inner ℝ (Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
        (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) z) z)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ u : CoordinateSpace n 4 → ℝ, ContDiff ℝ q u ∧ LatticePeriodic e lat u ∧
      (∀ x, r x = 0 → u x = 0) ∧
      (∀ x, r x < 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = g x) := by
  let T := latticeCellEquiv e lat c d
  let L : OAI.Analysis.PDE.Variational.CellVectors m ≃L[ℝ] CoordinateSpace n 4 := (rawCellEuclidean m).symm.trans T
  have hLT : cellPhysicalEquiv L = T := by
    apply ContinuousLinearEquiv.ext
    funext x
    change T ((rawCellEuclidean m).symm (rawCellEuclidean m x)) = T x
    rw [ContinuousLinearEquiv.symm_apply_apply]
  let A := fun x ↦ Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ)
    (mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x))
  have hAp : LatticePeriodic e lat A :=
    ((hψp.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp mooreRealMatrix).comp
      (Matrix.toEuclideanCLM (n := Fin n × Fin 4) (𝕜 := ℝ))
  obtain ⟨R, hR, htrans⟩ := exists_latticeCell_transverse_bound e lat c d hC hbounded
  let a := latticeCellLower d R
  let b := latticeCellUpper d R
  let J := latticeCellIndices d
  have hlen : ∀ i ∈ J, (b - a) i = 1 := latticeCell_period_length d R
  have hrT : ∀ z x, r (T (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z)) = r (T x) :=
    hrp.comp_latticeCellEquiv c d (b-a) hlen
  have hAT : ∀ z x, rawCellCoefficient L A (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) =
      rawCellCoefficient L A x := by
    intro z x
    have ha := hAp.comp_latticeCellEquiv c d (b-a) hlen z x
    change L.symm.toContinuousLinearMap.comp
        ((A (cellPhysicalEquiv L (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z))).comp
          L.symm.toContinuousLinearMap.adjoint) =
      L.symm.toContinuousLinearMap.comp
        ((A (cellPhysicalEquiv L x)).comp L.symm.toContinuousLinearMap.adjoint)
    rw [hLT]
    exact congrArg (fun B : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 ↦ L.symm.toContinuousLinearMap.comp
      (B.comp L.symm.toContinuousLinearMap.adjoint)) ha
  have hgT : ∀ z x, -(g (T (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z))) = -(g (T x)) := by
    intro z x
    rw [hgp.comp_latticeCellEquiv c d (b-a) hlen]
  have hregT : ∀ x, (r ∘ T) x = 0 → fderiv ℝ (r ∘ T) x ≠ 0 := by
    intro x hx hz
    have hder : fderiv ℝ (r ∘ T) x = (fderiv ℝ r (T x)).comp T.toContinuousLinearMap := by
      rw [fderiv_comp x (hr.differentiable (by simp) _) T.differentiableAt, T.fderiv]
    apply hreg (T x) hx
    ext y
    have hy := congrArg (fun B : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ ↦ B (T.symm y)) hz
    rw [hder] at hy
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using hy
  have hellT : ∀ x ∈ T ⁻¹' U, ∀ z : OAI.Analysis.PDE.Variational.CellVectors m,
      (lam / (‖L.toContinuousLinearMap‖ + 1)^2) * ‖z‖^2 ≤
        inner ℝ (rawCellCoefficient L A x z) z := by
    intro x hx z
    apply rawCellCoefficient_elliptic L A hlam.le
    simpa only [hLT] using hell (T x) hx
  have hlamT : 0 < lam / (‖L.toContinuousLinearMap‖ + 1)^2 := by positivity
  let k : Fin (m + 1) := d.symm (Sum.inr (Classical.choice (inferInstance : Nonempty κ)))
  have hk : k ∉ J := inr_not_mem_latticeCellIndices d _
  obtain ⟨v, hv, hvp, hvz, hve⟩ := OAI.Analysis.PDE.Weak.exists_smooth_periodic_dirichlet_solution J a b
    (latticeCellLower_le_upper d hR) (latticeCell_period_pos d R)
    (r ∘ T) (hr.comp T.contDiff) (fun z x hx ↦ by
      change r (T (x + OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z)) < 0 at hx
      rwa [hrT z x] at hx)
    k hk (rawCellCoefficient L A) (contDiff_rawCellCoefficient L hA) hAT
    (fun x ↦ -(g (T x))) (hg.comp T.contDiff).neg hgT
    (hU.preimage T.continuous) hlamT hellT hregT htrans
    (fun x hx ↦ hDU hx) q hq
  refine ⟨v ∘ T.symm, hv.comp T.symm.contDiff,
    latticePeriodic_of_coordinate_periodic e lat c d (b-a) hlen hvp, ?_, ?_⟩
  · intro x hx
    apply hvz
    simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hx
  · intro x hx
    have hxT : (r ∘ T) (T.symm x) < 0 := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hx
    have he := hve (T.symm x) hxT
    simp only [ContinuousLinearEquiv.apply_symm_apply] at he
    have h := moore_linearization_of_rawCell_equation L (hψ.of_le (by simp))
      (hv.of_le (by exact_mod_cast hq)) he
    simpa only [hLT, ContinuousLinearEquiv.apply_symm_apply] using h

end OAI.Analysis.PDE.Dirichlet
