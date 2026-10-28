import OAI.Analysis.DifferentialForms.Manifold.Open
import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws

/-! # Intrinsic Open Tangent -/

namespace OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent

noncomputable section

/-!
# Tangent transport for an intrinsic open submanifold

The actual inclusion of an open subset has a smooth local inverse. Its
manifold derivative therefore gives the tangent equivalence used to identify
ambient local covectors with covectors intrinsic to the open submanifold.
-/

open Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {U : Opens M} {n : ℕ}

theorem intrinsicOpenInverse_apply (hs : Nonempty U) (x : U) :
    (U.openPartialHomeomorphSubtypeCoe hs).symm (x : M) = x :=
  (U.openPartialHomeomorphSubtypeCoe hs).left_inv (by trivial)

/-- The local inverse of the inclusion is smooth at every point of the open set. -/
theorem intrinsicOpenInverse_contMDiffAt (hs : Nonempty U) {x : M} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (U.openPartialHomeomorphSubtypeCoe hs).symm x := by
  rw [← ContMDiffAt.subtypeVal_comp_iff]
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hs).right_inv
    (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

theorem intrinsicOpenInverse_contMDiffOn (hs : Nonempty U) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (U.openPartialHomeomorphSubtypeCoe hs).symm (U : Set M) :=
  fun _ hx => (intrinsicOpenInverse_contMDiffAt hs hx).contMDiffWithinAt

/-- The inclusion and its local inverse are genuinely manifold differentiable. -/
theorem intrinsicOpenInclusion_mdifferentiable (hs : Nonempty U) :
    (U.openPartialHomeomorphSubtypeCoe hs).MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) := by
  constructor
  · exact (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (U := U) (n := ∞)).mdifferentiable
      (by simp) |>.mdifferentiableOn
  · intro x hx
    have hxU : x ∈ (U : Set M) := by
      simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hx
    exact ((intrinsicOpenInverse_contMDiffAt (E := E) (U := U) hs hxU).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt

/-- The tangent equivalence is the actual derivative of open inclusion. -/
def intrinsicOpenTangentEquiv (x : U) :
    TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) :=
  (intrinsicOpenInclusion_mdifferentiable (E := E) (U := U) ⟨x⟩).mfderiv (by trivial)

@[simp]
theorem intrinsicOpenTangentEquiv_coe (x : U) :
    (intrinsicOpenTangentEquiv (E := E) x).toContinuousLinearMap =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x := rfl

/-- Any local inverse of the inclusion gives the inverse tangent derivative. -/
theorem intrinsicOpenTangentEquiv_symm_coe (hs : Nonempty U) (x : U) :
    (intrinsicOpenTangentEquiv (E := E) x).symm.toContinuousLinearMap =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (U.openPartialHomeomorphSubtypeCoe hs).symm (x : M) := by
  let other : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (x : M) :=
    (intrinsicOpenInclusion_mdifferentiable (E := E) hs).mfderiv (by trivial)
  have heq : intrinsicOpenTangentEquiv (E := E) x = other := by
    ext v
    rfl
  rw [heq]
  rfl

/-- Actual ambient local covectors and intrinsic covectors differ by tangent transport. -/
def intrinsicOpenRawEquiv (U : Opens M) (n : ℕ) :
    Open.RawOpenManifoldForm E U n ≃ₗ[ℂ] Algebra.RawManifoldForm E U n where
  toFun form x := (form x).compContinuousLinearMap
    (intrinsicOpenTangentEquiv (E := E) x).toContinuousLinearMap
  invFun form x := (form x).compContinuousLinearMap
    (intrinsicOpenTangentEquiv (E := E) x).symm.toContinuousLinearMap
  left_inv form := by
    funext x
    ext v
    change form x (fun i => intrinsicOpenTangentEquiv x
      ((intrinsicOpenTangentEquiv x).symm (v i))) = form x v
    congr 1
    funext i
    exact (intrinsicOpenTangentEquiv x).apply_symm_apply (v i)
  right_inv form := by
    funext x
    ext v
    change form x (fun i => (intrinsicOpenTangentEquiv x).symm
      (intrinsicOpenTangentEquiv x (v i))) = form x v
    congr 1
    funext i
    exact (intrinsicOpenTangentEquiv x).symm_apply_apply (v i)
  map_add' form other := by
    funext x
    ext v
    rfl
  map_smul' c form := by
    funext x
    ext v
    rfl

@[simp]
theorem intrinsicOpenRawEquiv_apply (form : Open.RawOpenManifoldForm E U n) (x : U) :
    intrinsicOpenRawEquiv U n form x = (form x).compContinuousLinearMap
      (intrinsicOpenTangentEquiv (E := E) x).toContinuousLinearMap := rfl

@[simp]
theorem intrinsicOpenRawEquiv_symm_apply (form : Algebra.RawManifoldForm E U n) (x : U) :
    (intrinsicOpenRawEquiv U n).symm form x = (form x).compContinuousLinearMap
      (intrinsicOpenTangentEquiv (E := E) x).symm.toContinuousLinearMap := rfl

/-- Forward tangent transport is precisely pullback of the auxiliary ambient extension. -/
theorem intrinsicOpenRawEquiv_eq_pullback (form : Open.RawOpenManifoldForm E U n) :
    intrinsicOpenRawEquiv U n form =
      (Open.openManifoldFormExtension U form).pullback (E := E) (Subtype.val : U → M) := by
  funext x
  change (form x).compContinuousLinearMap
      (intrinsicOpenTangentEquiv (E := E) x).toContinuousLinearMap =
    (Open.openManifoldFormExtension U form (x : M)).compContinuousLinearMap
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x)
  rw [Open.openManifoldFormExtension_apply, intrinsicOpenTangentEquiv_coe]

/-- The inverse transport agrees on its domain with pullback by a genuine local inverse. -/
theorem intrinsicOpenRawEquiv_symm_extension (hs : Nonempty U)
    (form : Algebra.RawManifoldForm E U n) {x : M} (hx : x ∈ U) :
    Open.openManifoldFormExtension U ((intrinsicOpenRawEquiv U n).symm form) x =
      form.pullback (E := E) (U.openPartialHomeomorphSubtypeCoe hs).symm x := by
  let point : U := ⟨x, hx⟩
  have hinv : (U.openPartialHomeomorphSubtypeCoe hs).symm x = point :=
    intrinsicOpenInverse_apply hs point
  change Open.openManifoldFormExtension U ((intrinsicOpenRawEquiv U n).symm form) (point : M) = _
  rw [Open.openManifoldFormExtension_apply, intrinsicOpenRawEquiv_symm_apply]
  rw [intrinsicOpenTangentEquiv_symm_coe hs point]
  unfold Algebra.RawManifoldForm.pullback
  rw [hinv]

end

end OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent
