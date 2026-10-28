import OAI.Analysis.DifferentialForms.Manifold.Basic
import OAI.Analysis.DifferentialForms.Manifold.ExteriorDerivative
import OAI.Analysis.DifferentialForms.Manifold.Derivative

/-! # Normed Space -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Agreement of normed-space and manifold differential forms

For the canonical identity atlas on a normed space, actual manifold cotangent
vectors identify with the usual alternating maps via the canonical tangent
space equivalence. This file identifies the two smooth-form constructions.
-/

open scoped _root_.Manifold ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

section

def Basic.RawForm.toManifold (form : Basic.RawForm E n) : Algebra.RawManifoldForm E E n :=
  fun x => (form x).compContinuousLinearMap
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).toContinuousLinearMap

end

section

def Algebra.RawManifoldForm.toNormedSpace (form : Algebra.RawManifoldForm E E n) : Basic.RawForm E n :=
  fun x => (form x).compContinuousLinearMap
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.toContinuousLinearMap

theorem Algebra.RawManifoldForm.inChart_refl (form : Algebra.RawManifoldForm E E n) :
    form.inChart (OpenPartialHomeomorph.refl E) = form.toNormedSpace := by
  funext x
  ext v
  change (form x) (fun i => (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (@id E) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (v i))) =
    (form x) (fun i => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (v i))
  rw [mfderiv_id]
  rfl

@[simp] theorem Algebra.RawManifoldForm.toNormedSpace_toManifold (form : Basic.RawForm E n) :
    form.toManifold.toNormedSpace = form := by
  funext x
  ext v
  change (form x) (fun i => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (v i))) = (form x) v
  apply congrArg (form x)
  funext i
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).apply_symm_apply (v i)

@[simp] theorem Algebra.RawManifoldForm.toManifold_toNormedSpace (form : Algebra.RawManifoldForm E E n) :
    form.toNormedSpace.toManifold = form := by
  funext x
  ext v
  change (form x) (fun i => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) (v i))) = (form x) v
  apply congrArg (form x)
  funext i
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm_apply_apply (v i)

theorem Algebra.RawManifoldForm.smooth_iff_contDiff_toNormedSpace (form : Algebra.RawManifoldForm E E n) :
    Algebra.IsSmoothManifoldFormOn form univ ↔ ContDiff ℝ ∞ form.toNormedSpace := by
  constructor
  · intro h
    have he := h (OpenPartialHomeomorph.refl E) (by simp)
    simpa [Algebra.RawManifoldForm.inChart_refl, Algebra.manifoldFormChartDomain, contDiffOn_univ] using he
  · intro h e he
    rw [chartedSpaceSelf_atlas] at he
    subst e
    simpa [Algebra.RawManifoldForm.inChart_refl, Algebra.manifoldFormChartDomain, contDiffOn_univ] using h

end

section

def Basic.SmoothForm.toManifold (form : Basic.SmoothForm E n) : Algebra.SmoothManifoldForm E E n :=
  ⟨(form : Basic.RawForm E n).toManifold,
    (Algebra.RawManifoldForm.smooth_iff_contDiff_toNormedSpace _).2
      (by simpa using form.smooth)⟩

end

section

def Algebra.SmoothManifoldForm.toNormedSpace (form : Algebra.SmoothManifoldForm E E n) : Basic.SmoothForm E n :=
  ⟨(form : Algebra.RawManifoldForm E E n).toNormedSpace,
    (Algebra.RawManifoldForm.smooth_iff_contDiff_toNormedSpace _).1 form.smooth⟩

end

/-- The two actual smooth-form models agree on a normed space. -/
def NormedSpace.smoothFormManifoldEquiv : Basic.SmoothForm E n ≃ₗ[ℂ] Algebra.SmoothManifoldForm E E n where
  toFun := Basic.SmoothForm.toManifold
  invFun := Algebra.SmoothManifoldForm.toNormedSpace
  left_inv form := by
    apply Subtype.ext
    exact Algebra.RawManifoldForm.toNormedSpace_toManifold (form : Basic.RawForm E n)
  right_inv form := by
    apply Subtype.ext
    exact Algebra.RawManifoldForm.toManifold_toNormedSpace (form : Algebra.RawManifoldForm E E n)
  map_add' form other := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl
  map_smul' c form := by
    apply Algebra.SmoothManifoldForm.ext
    intro x
    ext v
    rfl

theorem Algebra.SmoothManifoldForm.toNormedSpace_d (form : Algebra.SmoothManifoldForm E E n) :
    (Algebra.SmoothManifoldForm.d form).toNormedSpace = Basic.SmoothForm.d form.toNormedSpace := by
  apply Basic.SmoothForm.ext
  intro x
  have h := Algebra.SmoothManifoldForm.d_inChart form (OpenPartialHomeomorph.refl E)
    (by simp) (y := x) (by simp)
  change ((Algebra.SmoothManifoldForm.d form : Algebra.RawManifoldForm E E (n + 1)).toNormedSpace x) =
    extDeriv ((form : Algebra.RawManifoldForm E E n).toNormedSpace) x
  simpa only [Algebra.RawManifoldForm.inChart_refl] using h

theorem Basic.SmoothForm.toManifold_d (form : Basic.SmoothForm E n) :
    (Basic.SmoothForm.d form).toManifold = Algebra.SmoothManifoldForm.d form.toManifold := by
  apply Manifold.NormedSpace.smoothFormManifoldEquiv.symm.injective
  change (Basic.SmoothForm.d form).toManifold.toNormedSpace =
    (Algebra.SmoothManifoldForm.d form.toManifold).toNormedSpace
  rw [Algebra.SmoothManifoldForm.toNormedSpace_d]
  have hf : form.toManifold.toNormedSpace = form :=
    Manifold.NormedSpace.smoothFormManifoldEquiv.left_inv form
  have hd : (Basic.SmoothForm.d form).toManifold.toNormedSpace = Basic.SmoothForm.d form :=
    Manifold.NormedSpace.smoothFormManifoldEquiv.left_inv (Basic.SmoothForm.d form)
  rw [hf, hd]

end

end OAI.Analysis.DifferentialForms.Manifold
