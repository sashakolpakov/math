import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Nonzero
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-! # Projective -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Projective

noncomputable section

section

/-! The actual projective map of an original finite holomorphic section family with no common zero. -/

open _root_.TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {n : ℕ}
  (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : M, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x)

def holomorphicSectionFrameVector (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) : Fin (n + 1) → ℂ :=
  fun j => (s j).val i ⟨x.val, trivial, x.property⟩

include hs in
theorem holomorphicSectionFrameVector_nonzero (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicSectionFrameVector u s i x ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := hs x.val
  have hnj := (Nonzero.holomorphicSectionNonzeroAt_iff_frame u (s j) i x.val x.property).mp hj
  exact hnj (congrArg (fun a : Fin (n + 1) → ℂ => a j) hz)

def holomorphicSectionProjectiveMap (x : M) : Projectivization ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.mk ℂ (holomorphicSectionFrameVector u s x
    ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩)
    (holomorphicSectionFrameVector_nonzero u s hs x _)

theorem holomorphicSectionProjectiveMap_in_frame (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicSectionProjectiveMap u s hs x.val =
      Projectivization.mk ℂ (holomorphicSectionFrameVector u s i x)
        (holomorphicSectionFrameVector_nonzero u s hs i x) := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i x.val).val
    ⟨x.val, x.property, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val⟩, ?_⟩
  funext j
  exact ((s j).property i x.val x.val trivial x.property
    ((Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x.val)).symm

end

section

/-! The actual projective map of an original holomorphic generating family is continuous. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {n : ℕ}
  (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : M, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x)

theorem holomorphicSectionFrameVector_holomorphic (i : M) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin (n + 1) → ℂ) ∞ (holomorphicSectionFrameVector u s i) := by
  apply contMDiff_pi_space.mpr
  intro j
  exact (Data.holomorphicOpenRestriction (le_inf le_top le_rfl) ((s j).val i)).property

theorem holomorphicSectionProjectiveMap_continuous : Continuous (holomorphicSectionProjectiveMap u s hs) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let U := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x
  have hlocal : Continuous (fun y : U => holomorphicSectionProjectiveMap u s hs y.val) := by
    have hm := (ComplexPoints.Analytic.ProjectiveCompactness.continuous_projectivization_mk' ℂ (Fin (n + 1) → ℂ)).comp
      ((holomorphicSectionFrameVector_holomorphic u s x).continuous.subtype_mk
        (holomorphicSectionFrameVector_nonzero u s hs x))
    apply hm.congr
    intro y
    exact (holomorphicSectionProjectiveMap_in_frame u s hs x y).symm
  exact (continuousOn_iff_continuous_domRestrict.mpr hlocal).continuousAt
    (U.isOpen.mem_nhds ((Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x))

end

section

/-! Original section ratios are the actual affine coordinates of the constructed projective map and are holomorphic on their genuine nonvanishing patches. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {n : ℕ}
  (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : M, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x)

theorem holomorphicSectionProjectiveMap_inPatch (j : Fin (n + 1)) (x : M) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch j (holomorphicSectionProjectiveMap u s hs x) ↔ Nonzero.holomorphicSectionNonzeroAt u (s j) x :=
  Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_mk_iff j _ _

theorem holomorphicSectionProjectiveMap_ratio (i : M) (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (j k : Fin (n + 1)) :
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j k (holomorphicSectionProjectiveMap u s hs x.val) =
      (s k).val i ⟨x.val, trivial, x.property⟩ / (s j).val i ⟨x.val, trivial, x.property⟩ := by
  rw [holomorphicSectionProjectiveMap_in_frame, Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio_mk]
  rfl

theorem holomorphicSectionProjectiveMap_ratio_holomorphic (i : M) (j k : Fin (n + 1)) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ) ∞
      (fun x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j k (holomorphicSectionProjectiveMap u s hs x.val))
      {x | (s j).val i ⟨x.val, trivial, x.property⟩ ≠ 0} := by
  have hv := holomorphicSectionFrameVector_holomorphic u s i
  have hj := contMDiff_pi_space.mp hv j
  have hk := contMDiff_pi_space.mp hv k
  have hratio := hk.contMDiffOn.div₀ hj.contMDiffOn (fun x hx => hx)
  apply hratio.congr
  intro x _
  exact holomorphicSectionProjectiveMap_ratio u s hs i x j k

end

/-! The actual affine coordinate ratios of the constructed projective map are holomorphic at every original point in their patch. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) {n : ℕ}
  (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : M, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x)

theorem holomorphicSectionProjectiveMap_ratio_at (j k : Fin (n + 1)) (x : M)
    (hx : Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ) ∞ (fun y => Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio j k (holomorphicSectionProjectiveMap u s hs y)) x := by
  let U := Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x
  let y : U := ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩
  have hv := contMDiff_pi_space.mp (holomorphicSectionFrameVector_holomorphic u s x) j
  have ho : IsOpen {z : U | (s j).val x ⟨z.val, trivial, z.property⟩ ≠ 0} :=
    isOpen_ne_fun hv.continuous continuous_const
  have hy : y ∈ {z : U | (s j).val x ⟨z.val, trivial, z.property⟩ ≠ 0} := hx
  exact (contMDiffAt_subtype_iff (U := U) (x := y)).mp
    ((holomorphicSectionProjectiveMap_ratio_holomorphic u s hs x j k).contMDiffAt (ho.mem_nhds hy))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Projective
