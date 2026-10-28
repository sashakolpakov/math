import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.Analysis.DifferentialForms.Manifold.RelativeExtension

/-! # Supported Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms

noncomputable section

/-! Genuine supported extension of bundle-valued forms through their original transitions. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (u : Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ)
  (f : M → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f)

def holomorphicLineSmoothMul : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n →ₗ[ℂ]
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n where
  toFun s := ⟨fun i => Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn (s.val i), by
    intro i j x hx hi hj
    simp only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply]
    rw [s.property i j x hx hi hj, smul_comm]⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact map_add (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn) (s.val i) (t.val i)
  map_smul' z s := by
    apply Subtype.ext
    funext i
    exact map_smul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction f hf.contMDiffOn) z (s.val i)

theorem holomorphicLineSmoothMul_apply (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i : M)
    (x : ↥(U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) :
    (holomorphicLineSmoothMul u U n f hf s).val i x = f x • s.val i x :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.smulByFunction_apply f hf.contMDiffOn (s.val i) x

variable (hs : tsupport f ⊆ (U : Set M))

def holomorphicLineSupportedCoordinate (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) n :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtensionTo U
    (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) f hf.contMDiffOn hs).comp
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U ⊓ (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) ≤
        U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i from fun _ hx => ⟨hx.1, hx.2.2⟩))

theorem holomorphicLineSupportedCoordinate_apply_mem (i : M)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) n)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) (hx : (x : M) ∈ U) :
    holomorphicLineSupportedCoordinate u U n f hf hs i a x =
      f x • a ⟨x, hx, x.property.2⟩ := by
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtensionTo_apply_mem U
    (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) f hf.contMDiffOn hs _ x hx

theorem holomorphicLineSupportedCoordinate_apply_zero (i : M)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (U ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) n)
    (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) (hx : (x : M) ∉ tsupport f) :
    holomorphicLineSupportedCoordinate u U n f hf hs i a x = 0 := by
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtensionTo_eq_zero_of_notMem_tsupport U
    (⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i) f hf.contMDiffOn hs _ x hx

def holomorphicLineSupportedExtension : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n →ₗ[ℂ]
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n where
  toFun s := ⟨fun i => holomorphicLineSupportedCoordinate u U n f hf hs i (s.val i), by
    intro i j x hx hi hj
    by_cases hU : x ∈ U
    · rw [holomorphicLineSupportedCoordinate_apply_mem u U n f hf hs j _ ⟨x, hx, hj⟩ hU,
        holomorphicLineSupportedCoordinate_apply_mem u U n f hf hs i _ ⟨x, hx, hi⟩ hU,
        s.property i j x hU hi hj, smul_comm]
    · have hnot : x ∉ tsupport f := fun h => hU (hs h)
      rw [holomorphicLineSupportedCoordinate_apply_zero u U n f hf hs j _ ⟨x, hx, hj⟩ hnot,
        holomorphicLineSupportedCoordinate_apply_zero u U n f hf hs i _ ⟨x, hx, hi⟩ hnot]
      exact (smul_zero (A := TangentSpace 𝓘(ℝ, E) x [⋀^Fin n]→L[ℝ] ℂ)
        ((CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩)).symm⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact (holomorphicLineSupportedCoordinate u U n f hf hs i).map_add (s.val i) (t.val i)
  map_smul' z s := by
    apply Subtype.ext
    funext i
    exact (holomorphicLineSupportedCoordinate u U n f hf hs i).map_smul z (s.val i)

theorem holomorphicLineSupportedExtension_apply_mem (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : M) (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) (hx : (x : M) ∈ U) :
    (holomorphicLineSupportedExtension u U n f hf hs s).val i x =
      f x • s.val i ⟨x, hx, x.property.2⟩ :=
  holomorphicLineSupportedCoordinate_apply_mem u U n f hf hs i (s.val i) x hx

theorem holomorphicLineSupportedExtension_apply_zero (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n)
    (i : M) (x : ↥(⊤ ⊓ CohomologyTransitions.holomorphicCohomologyDomain E M u i)) (hx : (x : M) ∉ tsupport f) :
    (holomorphicLineSupportedExtension u U n f hf hs s).val i x = 0 :=
  holomorphicLineSupportedCoordinate_apply_zero u U n f hf hs i (s.val i) x hx

theorem holomorphicLineSupportedExtension_restrict (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top (holomorphicLineSupportedExtension u U n f hf hs s) =
      holomorphicLineSmoothMul u U n f hf s := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  change (holomorphicLineSupportedExtension u U n f hf hs s).val i ⟨x, trivial, x.property.2⟩ = _
  rw [holomorphicLineSupportedExtension_apply_mem u U n f hf hs s i _ x.property.1,
    holomorphicLineSmoothMul_apply]

theorem holomorphicLineSupportedExtension_of_global (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    holomorphicLineSupportedExtension u U n f hf hs (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict le_top s) =
      holomorphicLineSmoothMul u ⊤ n f hf s := by
  apply HolomorphicLine.AntiForms.holomorphicLineSmoothForm_ext
  intro i x
  rw [holomorphicLineSmoothMul_apply]
  by_cases hx : (x : M) ∈ U
  · rw [holomorphicLineSupportedExtension_apply_mem u U n f hf hs _ i x hx]
    rfl
  · have hnot : (x : M) ∉ tsupport f := fun h => hx (hs h)
    rw [holomorphicLineSupportedExtension_apply_zero u U n f hf hs _ i x hnot,
      image_eq_zero_of_notMem_tsupport hnot]
    exact (zero_smul ℂ (s.val i x)).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
