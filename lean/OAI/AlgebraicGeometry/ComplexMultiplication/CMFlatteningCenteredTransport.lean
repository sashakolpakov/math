import OAI.AlgebraicGeometry.ComplexMultiplication.CenteredFlatteningNormalPair
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Complex.Basic

/-! # CM Flattening Centered Transport -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CMFlatteningCenteredTransport

noncomputable section

section

/-! # Centering only the tangential coordinate preserves complex differentiability -/

open scoped _root_.Manifold

variable {M N E F G : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]

omit [TopologicalSpace M] in
theorem centeredFlatteningChart_mDifferentiable
    (f : M → N) (x : M) (e : OpenPartialHomeomorph N (E × F))
    (he : e.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) :
    (CenteredFlatteningNormalPair.centeredFlatteningChart f x e).MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F) := by
  apply he.trans
  constructor
  · intro y _
    exact (differentiableAt_id.sub (differentiableAt_const _)).mdifferentiableAt.mdifferentiableWithinAt
  · intro y _
    exact (differentiableAt_id.add (differentiableAt_const _)).mdifferentiableAt.mdifferentiableWithinAt

end

section

/-! # Transporting actual coordinate charts across proved dimension equalities -/

open scoped _root_.Manifold

variable {N G : Type*} [TopologicalSpace N] [NormedAddCommGroup G] [NormedSpace ℂ G]
  [ChartedSpace G N] {m n r p : ℕ}

/-- Only proved equal dimensions are transported; the chart and normal coordinate are unchanged. -/
def transportFlatteningChart (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ))) :
    OpenPartialHomeomorph N ((Fin r → ℂ) × (Fin p → ℂ)) :=
  hm ▸ hn ▸ e

omit [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N] in
@[simp] theorem transportFlatteningChart_source (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ))) :
    (transportFlatteningChart hm hn e).source = e.source := by
  subst r p
  rfl

omit [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N] in
theorem transportFlatteningChart_normal_zero (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ))) (y : N) :
    (transportFlatteningChart hm hn e y).2 = 0 ↔ (e y).2 = 0 := by
  subst r p
  rfl

theorem transportFlatteningChart_mDifferentiable (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ)))
    (he : e.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, (Fin m → ℂ) × (Fin n → ℂ))) :
    (transportFlatteningChart hm hn e).MDifferentiable
      𝓘(ℂ, G) 𝓘(ℂ, (Fin r → ℂ) × (Fin p → ℂ)) := by
  subst r p
  exact he

end

/-! # Proved tangential dimension transport leaves the genuine normal coordinate unchanged -/

variable {N : Type*} [TopologicalSpace N] {m n r p : ℕ}

theorem transportFlatteningChart_normal_coordinate (hm : m = r) (hn : n = p)
    (e : OpenPartialHomeomorph N ((Fin m → ℂ) × (Fin n → ℂ))) (y : N) :
    (transportFlatteningChart hm hn e y).2 =
      (transportFlatteningChart rfl hn e y).2 := by
  subst r p
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CMFlatteningCenteredTransport
