/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

/-! # Analytic Left At -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Analytic local left inverses from section lifting

-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace Filter

section

universe u

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- Any family of sections on an intrinsic open lifts, after restriction, on a single
affine ambient neighborhood of the selected point. The lifts come from the
surjective closed-immersion map on affine sections. -/
theorem ClosedImmersion.AnalyticLeftAt.Scheme.Hom.exists_affine_local_section_lifts
    {J : Type*} (V : Y.Opens) (s : J → Γ(Y, V)) (y : Y) (hy : y ∈ V) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (hUV : i ⁻¹ᵁ U ≤ V),
      i y ∈ U ∧ ∃ r : J → Γ(X, U),
        ∀ j, i.app U (r j) = Y.presheaf.map (homOfLE hUV).op (s j) := by
  obtain ⟨W, hW, hpre⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  have hyW : i y ∈ W := show y ∈ ⇑i ⁻¹' W from hpre ▸ hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hyW hW
  have hUV : i ⁻¹ᵁ U ≤ V := fun z hz ↦ show z ∈ (V : Set Y) from hpre ▸ hUW hz
  choose r hr using fun j => i.app_surjective U hU
    (Y.presheaf.map (homOfLE hUV).op (s j))
  exact ⟨U, hU, hUV, hyU, r, hr⟩

end

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]

@[simp] theorem ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z) =
        ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z) := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts
  rw [(ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).left_inv (ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z)]

/-- Analyticity is inherited from the morphism of smooth schemes. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    AnalyticAt ℂ (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z) := by
  apply ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_map Y X i m d z
    ((ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).map_source (ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z))
  rw [(ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z).left_inv (ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z)]
  exact ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (ComplexPoint.Basic.Point.map i z)

/-- A smooth closed immersion has an analytic local left inverse in complex coordinates,
obtained by lifting the intrinsic coordinate sections. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_analytic_localLeftInverse_of_isClosedImmersion [IsClosedImmersion i.left]
    (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ∃ L : (Fin d → ℂ) → (Fin m → ℂ),
      AnalyticAt ℂ L
        (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
          (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)) ∧
      (L ∘ ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z) =ᶠ[
        𝓝 (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)] id := by
  let D := ComplexPoint.Basic.ComplexSchemePoint.localEtaleCoordinates Y m z
  have hzD : z.underlying ∈ D.ambientCoordinateOpen := by
    simpa only [D, ComplexPoint.SmoothCoordinates.LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top,
      ComplexPoint.Basic.Point.overOpen, Set.mem_ofPred_eq] using
      ComplexPoint.Basic.ComplexSchemePoint.mem_localEtaleCoordinates Y m z
  obtain ⟨U, _hU, hUV, hzU, r, hr⟩ := (ClosedImmersion.AnalyticLeftAt.Scheme.Hom.exists_affine_local_section_lifts i.left)
    D.ambientCoordinateOpen D.ambientCoordinateSection z.underlying hzD
  let eY := ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z
  let eX := ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z)
  let L : (Fin d → ℂ) → (Fin m → ℂ) :=
    fun w j => ComplexPoint.Basic.Point.evaluate U (r j) (eX.symm w)
  have hzY : z ∈ eY.source := ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z
  have hzX : ComplexPoint.Basic.Point.map i z ∈ eX.source :=
    ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (ComplexPoint.Basic.Point.map i z)
  have hzYt : eY z ∈ eY.target := eY.map_source hzY
  have hzXt : eX (ComplexPoint.Basic.Point.map i z) ∈ eX.target := eX.map_source hzX
  refine ⟨L, ?_, ?_⟩
  · rw [ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center]
    refine AnalyticAt.pi fun j ↦ ?_
    apply ComplexPoint.Basic.ComplexSchemePoint.analyticAt_localChart_symm_evaluate X d (ComplexPoint.Basic.Point.map i z) hzXt U (r j)
    change eX.symm (eX (ComplexPoint.Basic.Point.map i z)) ∈ ComplexPoint.Basic.Point.overOpen U
    rw [eX.left_inv hzX]
    exact hzU
  · have hc : ContinuousAt (fun v => ComplexPoint.Basic.Point.map i (eY.symm v)) (eY z) :=
      (ComplexPoint.Basic.Point.continuous_map i).continuousAt.comp (eY.continuousAt_symm hzYt)
    have hX : ∀ᶠ v in 𝓝 (eY z), ComplexPoint.Basic.Point.map i (eY.symm v) ∈ eX.source := by
      apply hc (eX.open_source.mem_nhds _)
      change ComplexPoint.Basic.Point.map i (eY.symm (eY z)) ∈ eX.source
      rw [eY.left_inv hzY]
      exact hzX
    have hU : ∀ᶠ v in 𝓝 (eY z), ComplexPoint.Basic.Point.map i (eY.symm v) ∈ ComplexPoint.Basic.Point.overOpen U := by
      apply hc ((ComplexPoint.Basic.Point.isOpen_overOpen U).mem_nhds _)
      change ComplexPoint.Basic.Point.map i (eY.symm (eY z)) ∈ ComplexPoint.Basic.Point.overOpen U
      rw [eY.left_inv hzY]
      exact hzU
    filter_upwards [eY.open_target.mem_nhds hzYt, hX, hU] with v hvY hvX hvU
    funext j
    change ComplexPoint.Basic.Point.evaluate U (r j)
      (eX.symm (eX (ComplexPoint.Basic.Point.map i (eY.symm v)))) = v j
    rw [eX.left_inv hvX, ComplexPoint.Basic.Point.evaluate_map, hr,
      ← ComplexPoint.Basic.Point.evaluate_res hUV (D.ambientCoordinateSection j) (eY.symm v)
        ((ComplexPoint.Basic.Point.mem_overOpen_map_iff i _ U).mp hvU),
      ← ComplexPoint.Basic.ComplexSchemePoint.localChart_apply_component_eq_evaluate Y m z (eY.symm v) (eY.map_target hvY) j]
    exact congrFun (eY.right_inv hvY) j

/-- The derivative of a smooth closed immersion has a continuous-linear left
inverse, obtained by differentiating the analytic local left inverse. -/
theorem ComplexPoint.Basic.ComplexSchemePoint.exists_leftInverse_fderiv_inclusionInComplexCharts [IsClosedImmersion i.left]
    (z : ComplexPoint.Basic.ComplexSchemePoint Y) :
    ∃ P : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ),
      P.comp (fderiv ℂ (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) := by
  obtain ⟨L, hL, hleft⟩ :=
    ComplexPoint.Basic.ComplexSchemePoint.exists_analytic_localLeftInverse_of_isClosedImmersion X Y i m d z
  let φ := ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z
  let a := ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z
  refine ⟨fderiv ℂ L (φ a), ?_⟩
  have hφ := ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z
  have hc := hL.differentiableAt.hasFDerivAt.comp a hφ.differentiableAt.hasFDerivAt
  exact (hc.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id a)

end

end OAI.AlgebraicGeometry
