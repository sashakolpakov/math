import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm

/-! # Scalar Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.ScalarAction

noncomputable section

/-! Actual multiplication of bundle-valued smooth forms by a smooth scalar function. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {U : Opens M} (n : ℕ)

def holomorphicLineSmoothScalarMul (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n where
  toFun a := ⟨fun i => SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarForm.smoothComplexOpenFunctionRestrict inf_le_left f) (a.val i), by
    intro i j x hx hi hj
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply]
    change f ⟨x, hx⟩ • a.val j ⟨x, hx, hj⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ • (f ⟨x, hx⟩ • a.val i ⟨x, hx, hi⟩)
    rw [a.property i j x hx hi hj, smul_comm]⟩
  map_add' a b := by
    apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
    intro i x
    change (SmoothScalarForm.smoothScalarOpenFormMul _ (a.val i + b.val i)) x = _
    rw [map_add]
    rfl
  map_smul' z a := by
    apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
    intro i x
    change (SmoothScalarForm.smoothScalarOpenFormMul _ (z • a.val i)) x = _
    rw [map_smul]
    rfl

theorem holomorphicLineSmoothScalarMul_apply (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : M)
    (x : ↥(U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
    (holomorphicLineSmoothScalarMul u n f a).val i x = f ⟨x.val, x.property.1⟩ • a.val i x :=
  SmoothScalarForm.smoothScalarOpenFormMul_apply _ _ x

theorem holomorphicLineSmoothScalarMul_comp (f g : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    holomorphicLineSmoothScalarMul u n f (holomorphicLineSmoothScalarMul u n g a) =
      holomorphicLineSmoothScalarMul u n (SmoothScalarForm.smoothComplexOpenFunctionMul f g) a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  rw [holomorphicLineSmoothScalarMul_apply, holomorphicLineSmoothScalarMul_apply,
    holomorphicLineSmoothScalarMul_apply, smul_smul]
  rfl

theorem holomorphicLineSmoothScalarMul_one (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) (hf : ∀ x, f x = 1) :
    holomorphicLineSmoothScalarMul u n f a = a := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  rw [holomorphicLineSmoothScalarMul_apply, hf, one_smul]

theorem holomorphicLineSmoothScalarMul_restrict {W : Opens M} (h : W ≤ U)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict h (holomorphicLineSmoothScalarMul u n f a) =
      holomorphicLineSmoothScalarMul u n (SmoothScalarForm.smoothComplexOpenFunctionRestrict h f)
        (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict h a) := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  change (holomorphicLineSmoothScalarMul u n f a).val i ⟨x.val, h x.property.1, x.property.2⟩ = _
  rw [holomorphicLineSmoothScalarMul_apply, holomorphicLineSmoothScalarMul_apply]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.ScalarAction
