import OAI.Analysis.DifferentialForms.Manifold.PullbackLaws
import OAI.Analysis.DifferentialForms.Manifold.TangentCoordinates
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Invariant Closed -/

namespace OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology

noncomputable section

section

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}

def invariantRawForm (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n :=
  fun g => α.compContinuousLinearMap
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun h : G => g⁻¹ * h) g)

omit [LieGroup 𝓘(ℝ, E) ∞ G] in
theorem invariantRawForm_one
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) :
    invariantRawForm α 1 = α := by
  have h : (fun h : G => (1 : G)⁻¹ * h) = id := by funext h; simp
  unfold invariantRawForm
  rw [h, mfderiv_id]
  ext v
  rfl

theorem invariantRawForm_pullback
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) (g : G) :
    (invariantRawForm α).pullback (fun x : G => g * x) = invariantRawForm α := by
  funext x
  ext v
  have hcomp : (fun h : G => (g * x)⁻¹ * h) ∘ (fun h : G => g * h) =
      (fun h : G => x⁻¹ * h) := by
    funext h
    simp [mul_assoc]
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) x
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞) (a := (g * x)⁻¹)).mdifferentiableAt (by simp))
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞) (a := g)).mdifferentiableAt (by simp))
  rw [hcomp] at hd
  simp only [OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_apply, invariantRawForm,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def]
  apply congrArg α
  funext i
  exact (congrArg (fun f => f (v i)) hd).symm

theorem invariantRawForm_inChart
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ)
    (c d : OpenPartialHomeomorph G E) (hc : c ∈ atlas E G) (hd : d ∈ atlas E G)
    (h1 : (1 : G) ∈ d.source) {y : E} (hy : y ∈ c.target) :
    (invariantRawForm α).inChart c y =
      (α.compContinuousLinearMap (OAI.Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1))).compContinuousLinearMap
        (fderiv ℝ (fun w => d ((c.symm y)⁻¹ * c.symm w)) y) := by
  let β : OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E G n := fun _ => α
  have hp := β.pullback_inChart (fun h : G => (c.symm y)⁻¹ * h) c d hc hd hy
    (by simpa using h1)
    ((contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp))
  have he : (c.symm y)⁻¹ * c.symm y = 1 := inv_mul_cancel _
  rw [he] at hp
  simpa only [OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart, OAI.Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback, β,
    invariantRawForm, OAI.Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap, Function.comp_def] using! hp

theorem invariantRawForm_smooth
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (invariantRawForm α) univ := by
  intro c hc y hy
  let d := chartAt E (1 : G)
  have hd : d ∈ atlas E G := chart_mem_atlas E (1 : G)
  have h1 : (1 : G) ∈ d.source := mem_chart_source E (1 : G)
  have hcinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy.1
  have hc₁ : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
      (fun z : E × E => c.symm z.1) (y, y) :=
    hcinv.comp (y, y) contDiffAt_fst.contMDiffAt
  have hc₂ : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
      (fun z : E × E => c.symm z.2) (y, y) :=
    hcinv.comp (y, y) contDiffAt_snd.contMDiffAt
  have hm : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞
      (fun z : E × E => (c.symm z.1)⁻¹ * c.symm z.2) (y, y) := hc₁.inv.mul hc₂
  have hd' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ d
      ((c.symm y)⁻¹ * c.symm y) := by
    rw [inv_mul_cancel]
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) h1
  have ht : ContDiffAt ℝ ∞
      (fun z : E × E => d ((c.symm z.1)⁻¹ * c.symm z.2)) (y, y) :=
    (hd'.comp (y, y) hm).contDiffAt
  have hder : ContDiffAt ℝ ∞
      (fun z => fderiv ℝ (fun w => d ((c.symm z)⁻¹ * c.symm w)) z) y :=
    ht.fderiv contDiffAt_id (by simp)
  have hsm := OAI.Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap
    (contDiffAt_const (c := α.compContinuousLinearMap (OAI.Analysis.DifferentialForms.Manifold.Charts.chartInverseTangentMap d (d 1)))) hder
  apply (hsm.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [c.open_target.mem_nhds hy.1] with z hz
  exact invariantRawForm_inChart α c d hc hd h1 hz

def invariantForms (n : ℕ) : Submodule ℂ (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :=
  ⨅ g : G, LinearMap.ker
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => g * x)
      (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) - LinearMap.id)

theorem mem_invariantForms_iff (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    form ∈ invariantForms (E := E) (G := G) n ↔ ∀ g : G,
      OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => g * x)
        (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form = form := by
  simp only [invariantForms, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

def invariantSmoothForm
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n := ⟨invariantRawForm α, invariantRawForm_smooth α⟩

theorem invariantSmoothForm_mem
    (α : TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) :
    invariantSmoothForm α ∈ invariantForms (E := E) (G := G) n := by
  rw [mem_invariantForms_iff]
  intro g
  apply Subtype.ext
  exact invariantRawForm_pullback α g

theorem invariantForm_eq_from_value (form : invariantForms (E := E) (G := G) n) :
    invariantSmoothForm (form.val 1) = form.val := by
  apply OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have hi := (mem_invariantForms_iff form.val).mp form.property x⁻¹
  have hv := congrArg (fun η : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n => η x) hi
  rw [OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_apply, inv_mul_cancel] at hv
  exact hv

def invariantFormsEvalEquiv (n : ℕ) :
    invariantForms (E := E) (G := G) n ≃ₗ[ℂ]
      (TangentSpace 𝓘(ℝ, E) (1 : G) [⋀^Fin n]→L[ℝ] ℂ) where
  toFun form := form.val 1
  invFun α := ⟨invariantSmoothForm α, invariantSmoothForm_mem α⟩
  left_inv form := Subtype.ext (invariantForm_eq_from_value form)
  right_inv α := invariantRawForm_one α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

/-!
# Closed invariant forms for ExteriorCohomology

On a commutative real Lie group, inversion acts on invariant degree-n forms
by (-1)^n. Naturality of the exterior derivative then proves that every
invariant form is closed. No compactness or cohomology comparison is assumed.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G]

theorem mfderiv_mul_one (v w : E) :
    mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
      (fun p : G × G => p.1 * p.2) (1, 1) (v, w) = v + w := by
  have hp := mfderiv_prod_eq_add_apply (v := (v, w))
    ((contMDiff_mul 𝓘(ℝ, E) ∞).mdifferentiableAt (x := ((1 : G), 1)) (by simp))
  have hl : (fun z : G => z * 1) = id := funext mul_one
  have hr : (fun z : G => 1 * z) = id := funext one_mul
  dsimp only at hp
  rw [hl, hr, mfderiv_id] at hp
  exact hp

theorem mfderiv_inv_one (v : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 v = -v := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 :=
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (by simp)
  have hc := mfderiv_comp (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, E).prod 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E)) (1 : G)
    ((contMDiff_mul 𝓘(ℝ, E) ∞).mdifferentiableAt (by simp))
    (mdifferentiableAt_id.prodMk hi)
  have he : (fun p : G × G => p.1 * p.2) ∘ (fun x : G => (x, x⁻¹)) =
      fun _ => (1 : G) := by funext x; simp
  simp only [id_eq] at hc
  rw [he] at hc
  rw [mfderiv_const, inv_one] at hc
  have hp := mfderiv_prodMk (I := 𝓘(ℝ, E)) mdifferentiableAt_id hi
  dsimp only [id_eq] at hp
  rw [hp, mfderiv_id] at hc
  have hv := congrArg (fun f : E →L[ℝ] E => f v) hc
  change 0 = mfderiv (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
    (fun p : G × G => p.1 * p.2) (1, 1)
    (v, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 v) at hv
  have hz := hv.trans (mfderiv_mul_one (E := E) (G := G) v
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 v))
  exact eq_neg_of_add_eq_zero_right hz.symm

theorem inverse_mfderiv_inv (g : G) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) g).inverse =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) g⁻¹ := by
  have hi : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) :=
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiable (by simp)
  have he : (Inv.inv : G → G) ∘ Inv.inv = id := by funext x; simp
  have h₁ := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    g (hi g⁻¹) (hi g)
  have h₂ := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := 𝓘(ℝ, E))
    g⁻¹ (hi (g⁻¹)⁻¹) (hi g⁻¹)
  rw [he, mfderiv_id] at h₁ h₂
  rw [inv_inv] at h₂
  exact ContinuousLinearMap.inverse_eq h₂.symm h₁.symm

variable {n : ℕ}

theorem d_mem_invariantForms (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ invariantForms (E := E) (G := G) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form ∈ invariantForms (E := E) (G := G) (n + 1) := by
  rw [mem_invariantForms_iff] at hf ⊢
  intro g
  rw [← OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback, hf g]

variable [IsMulCommutative G]

theorem inv_pullback_mem_invariantForms (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ invariantForms (E := E) (G := G) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Inv.inv : G → G)
      (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)) form ∈
        invariantForms (E := E) (G := G) n := by
  rw [mem_invariantForms_iff] at hf ⊢
  intro g
  have he : (Inv.inv : G → G) ∘ (fun x : G => g * x) =
      (fun x : G => g⁻¹ * x) ∘ Inv.inv := by
    funext x
    simp only [Function.comp_apply, mul_inv_rev, mul_comm']
  rw [← OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  simp only [he]
  have hp := OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp (Inv.inv : G → G)
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)) (fun x : G => g⁻¹ * x)
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form
  rw [hf g⁻¹] at hp
  exact hp

omit [IsMulCommutative G] in
theorem inv_pullback_one (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    (OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Inv.inv : G → G)
      (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)) form) 1 =
        (-1 : ℂ) ^ n • form 1 := by
  rw [OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_apply]
  rw [inv_one]
  ext v
  change (form 1) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 (v i)) =
    ((-1 : ℂ) ^ n) * (form 1) v
  have hs := (form 1).toAlternatingMap.map_smul_univ (fun _ : Fin n => (-1 : ℝ)) v
  have he : (fun i : Fin n => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Inv.inv : G → G) 1 (v i)) =
      (fun i => (-1 : ℝ) • v i) := by
    funext i
    exact (mfderiv_inv_one (E := E) (G := G) (v i)).trans (neg_one_smul ℝ (v i)).symm
  exact (congrArg (form 1) he).trans (by simpa using hs)

theorem inv_pullback_invariant (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ invariantForms (E := E) (G := G) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Inv.inv : G → G)
      (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)) form = (-1 : ℂ) ^ n • form := by
  let lhs : invariantForms (E := E) (G := G) n :=
    ⟨_, inv_pullback_mem_invariantForms form hf⟩
  let rhs : invariantForms (E := E) (G := G) n :=
    ⟨_, (invariantForms (E := E) (G := G) n).smul_mem ((-1 : ℂ) ^ n) hf⟩
  have he : lhs = rhs := (invariantFormsEvalEquiv n).injective (inv_pullback_one form)
  exact congrArg Subtype.val he

theorem invariantForms_closed (form : OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ invariantForms (E := E) (G := G) n) :
    OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 := by
  have h := OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback (Inv.inv : G → G)
    (contMDiff_inv (I := 𝓘(ℝ, E)) (n := ∞)) form
  rw [inv_pullback_invariant form hf, map_smul,
    inv_pullback_invariant _ (d_mem_invariantForms form hf)] at h
  have hsign : (-1 : ℂ) ^ n ≠ (-1 : ℂ) ^ (n + 1) := by
    rw [pow_succ]
    intro he
    have hmul := (mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr one_ne_zero)))
      (show (-1 : ℂ) ^ n * 1 = (-1 : ℂ) ^ n * (-1) by simpa using he)
    norm_num at hmul
  have hzero : ((-1 : ℂ) ^ n - (-1 : ℂ) ^ (n + 1)) • OAI.Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hsign)

end

end OAI.AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology
