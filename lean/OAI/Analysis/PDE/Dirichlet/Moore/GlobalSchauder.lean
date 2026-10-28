import OAI.Analysis.PDE.Dirichlet.Moore.GlobalSchauderGeometry
import OAI.Analysis.PDE.Dirichlet.Moore.GlobalSchauderCoefficient
import OAI.Analysis.PDE.Dirichlet.SchauderIsometryEquation
import OAI.Analysis.PDE.Dirichlet.Uniform.Schauder
import OAI.Analysis.PDE.Dirichlet.Rough.Moore

/-! The actual Moore operators satisfy the uniform periodic Schauder
estimate.  The analytic estimate is proved by the global periodic Schauder
theorem, and the change of coordinates is isometric on the stored jets. -/

open Set Module InnerProductSpace
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance mooreGlobalFirstGroup : NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance mooreGlobalFirstSpace : NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance mooreGlobalSecondGroup : NormedAddCommGroup
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance mooreGlobalSecondSpace : NormedSpace ℝ
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

/-- Uniform Schauder control for the genuine linearized Moore equation.
There is no assumed analytic estimate, inverse, or existence premise. -/
theorem uniform_periodic_moore_schauder
    (hn : 1 ≤ n) (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    (r : CoordinateSpace n 4 → ℝ) (hr : ContDiff ℝ 3 r)
    (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    UniformPeriodicMooreSchauderEstimate e b hΩD α := by
  intro lam M hlam hM
  let L := (flattenFourSlots n).symm
  let e' := L.toContinuousLinearEquiv.trans e
  let r' := r ∘ L
  have hgeometry := fourSlot_schauder_geometry e b hr hrp hbounded hreg
  have hΩD' : L ⁻¹' {x | r x < 0} ⊆ L ⁻¹' {x | r x ≤ 0} := preimage_mono hΩD
  obtain ⟨C, hC, hest⟩ := uniform_periodic_schauder (m := n * 4) (by omega)
    e' b hK r' hgeometry.1 hgeometry.2.1 hgeometry.2.2.1 hgeometry.2.2.2
    (hΩD := hΩD') hα hα1 hlam hM.le hM.le
  refine ⟨C, hC, ?_⟩
  intro ψ hψ _hψp _hpos hlower hnorm hholder B hB F hFn hFh U _hUD u hu hup hu0 hU0 hU1 hU2 heq
  let A := fun x => detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
  let A' := fun x => isometryConjugate L (A (L x))
  have hAc : Continuous A := continuous_moore_schauder_coefficient (hψ.of_le (by simp))
  have hA'c : Continuous A' := continuous_isometryConjugate_field L A hAc
  have hA's : ∀ x, r' x ≤ 0 → (A' x).toLinearMap.IsSymmetric := by
    intro x _
    exact isometryConjugate_isSymmetric L _ (detRealOperator_isSymmetric _)
  have hA'l : ∀ x, r' x ≤ 0 → ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A' x v) := by
    intro x hx v
    calc
      lam * ‖v‖ ^ 2 = lam * ‖L v‖ ^ 2 := by rw [L.norm_map]
      _ ≤ inner ℝ (L v) (A (L x) (L v)) := hlower (L x) hx (L v)
      _ = inner ℝ (A (L x) (L v)) (L v) := real_inner_comm _ _
      _ = inner ℝ (A' x v) v := (inner_isometryConjugate L (A (L x)) v v).symm
      _ = inner ℝ v (A' x v) := real_inner_comm _ _
  have hA'n : ∀ x, r' x ≤ 0 → ‖A' x‖ ≤ M := by
    intro x hx
    simpa only [A', norm_isometryConjugate] using hnorm (L x) hx
  have hA'u : ∀ x, r' x ≤ 0 → ∀ v, inner ℝ v (A' x v) ≤ M * ‖v‖ ^ 2 := by
    intro x hx v
    exact inner_operator_upper_of_norm_le _ (hA'n x hx) v
  have hA'h : ∀ x, r' x ≤ 0 → ∀ y, r' y ≤ 0 →
      ‖A' x - A' y‖ ≤ M * dist x y ^ α := by
    intro x hx y hy
    exact isometryConjugate_holder L A hholder hx hy
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  obtain ⟨W, hwu, hWnorm, hW0, hW1, hW2⟩ :=
    exists_C2Holder_isometry_pullback hΩ hΩD hα.le L u hu U hU0 hU1 hU2
  have hwperiodic : LatticePeriodic e' b (u ∘ L) := hup.comp_domain_equiv L.toContinuousLinearEquiv
  have hwzero : ∀ x, r' x = 0 → (u ∘ L) x = 0 := by
    intro x hx
    change r (L x) = 0 at hx
    exact hu0 (L x) hx.le (not_lt.mpr hx.ge)
  have hF'n : ∀ x, r' x ≤ 0 → |(F ∘ L) x| ≤ B := by
    intro x hx
    exact hFn ⟨L x, hx⟩
  have hF'h : ∀ x, r' x ≤ 0 → ∀ y, r' y ≤ 0 →
      |(F ∘ L) x - (F ∘ L) y| ≤ B * dist x y ^ α := by
    intro x hx y hy
    simpa only [Function.comp_apply, Subtype.dist_eq, L.isometry.dist_eq] using
      hFh ⟨L x, hx⟩ ⟨L y, hy⟩
  have heq' : ∀ x, r' x ≤ 0 → OAI.Analysis.PDE.Elliptic.ellipticTrace A' (u ∘ L) x = (F ∘ L) x := by
    intro x hx
    rw [ellipticTrace_isometry_pullback L A u (hu.of_le (by norm_num))]
    exact ellipticTrace_eq_of_moore_jet_equation
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u (hu.of_le (by norm_num)) U hU2 F heq (L x) hx
  have hWvalue : ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value W‖ ≤ ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value U‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro x
    rw [hW0, ← hU0 ⟨L x, x.property⟩]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.value U).norm_coe_le_norm _
  calc
    ‖U‖ = ‖W‖ := hWnorm.symm
    _ ≤ C * (B + ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value W‖) :=
      hest A' hA'c hA's hA'l hA'u hA'n hA'h (u ∘ L) hwu hwperiodic hwzero
        (F ∘ L) B hB hF'n hF'h heq' W hW0 hW1 hW2
    _ ≤ C * (B + ‖OAI.Analysis.Normed.Function.Holder.C2Holder.value U‖) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hWvalue) hC.le

end OAI.Analysis.PDE.Dirichlet
