import OAI.AlgebraicTopology.Cohomology.Singular.OpenCechTransport
import OAI.AlgebraicTopology.Cohomology.Singular.OpenCochainPresheafComparison

/-! # Smooth Relative Cech Transport -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.SmoothRelativeCechTransport

noncomputable section

/-!
# Smooth Čech descent for a cover of an actual open subset

Pulling an ambient open family back to the open submanifold gives a genuine
cover there. Its finite intersections flatten to the original intersections.
The proved nested-open smooth presheaf identification then transports the
whole-space augmentation to the canonical relative-open augmentation.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section OpenDomains

variable {X ι : Type} [TopologicalSpace X]
variable (U : ι → Opens X) (W : Opens X)

/-- Regard the ambient open family as a family in the containing open subset. -/
def relativeCechOpenCover (i : ι) : Opens W :=
  Opens.comap (⟨Subtype.val, continuous_subtype_val⟩ : C(W, X)) (U i)

@[simp]
theorem mem_relativeCechOpenCover (i : ι) (x : W) :
    x ∈ relativeCechOpenCover U W i ↔ (x : X) ∈ U i := Iff.rfl

/-- A cover of the open domain is an actual whole-space cover of its subtype. -/
theorem relativeCechOpenCover_covers
    (hcover : ∀ x : W, ∃ i, (x : X) ∈ U i) :
    ∀ x : W, ∃ i, x ∈ relativeCechOpenCover U W i := hcover

/-- Flattening the top open subset of an open subtype recovers the original
open domain exactly. -/
theorem relativeCechOpenImage_top :
    (OpenCochainPresheafComparison.nestedOpenImageFunctor W).obj (⊤ : Opens W) = W := by
  change ChartOpenDiffeomorph.nestedOpenImage W ⊤ = W
  ext x
  constructor
  · rintro ⟨y, _, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩

variable (hsub : ∀ i, U i ≤ W)

include hsub in
/-- Each finite nonempty intersection in the open-subspace cover flattens
to the exact original ambient intersection. -/
theorem relativeCechOpenCover_intersection_image (n : ℕ)
    (a : Fin (n + 1) → ι) :
    (OpenCochainPresheafComparison.nestedOpenImageFunctor W).obj (DeRham.Comparison.SmoothCech.cechIntersection (relativeCechOpenCover U W) a) =
      DeRham.Comparison.SmoothCech.cechIntersection U a := by
  change ChartOpenDiffeomorph.nestedOpenImage W (DeRham.Comparison.SmoothCech.cechIntersection (relativeCechOpenCover U W) a) = _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (DeRham.Comparison.SmoothCech.mem_cechIntersection U a (y : X)).2
    intro j
    exact (DeRham.Comparison.SmoothCech.mem_cechIntersection (relativeCechOpenCover U W) a y).1 hy j
  · intro hx
    have hxW := DeRham.Comparison.CechComplexAugmentation.cechIntersection_le_openDomain U W hsub a hx
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    apply (DeRham.Comparison.SmoothCech.mem_cechIntersection (relativeCechOpenCover U W) a ⟨x, hxW⟩).2
    intro j
    exact (DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).1 hx j

end OpenDomains

variable (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace X] [ChartedSpace E X]
variable {ι : Type} (U : ι → Opens X) (W : Opens X) (hsub : ∀ i, U i ≤ W)
variable (A : ModuleCat.{0} ℂ)

/-- The relative-open augmentation and the native whole-space augmentation
on the open submanifold are isomorphic as actual arrows of complexes. -/
def manifoldSmoothRelativeCechAugmentationArrowIso :
    Arrow.mk (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation U W hsub (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A)) ≅
      Arrow.mk (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation (relativeCechOpenCover U W) ⊤ (fun _ => le_top)
        (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E W A)) := by
  let e := OpenCochainPresheafComparison.manifoldSmoothOpenPresheafComplexIso E X A W
  exact OpenCechTransport.cechSpaceTransportAugmentationArrowIso (OpenCochainPresheafComparison.nestedOpenImageFunctor W) U
    (relativeCechOpenCover U W) (relativeCechOpenCover_intersection_image U W hsub)
    (ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E X A) W ⊤ (relativeCechOpenImage_top W)
    hsub (fun _ => le_top) ≪≫
      Arrow.isoMk
        ((DeRham.Comparison.CechComplexAugmentation.presheafComplexSectionsFunctor (⊤ : Opens W)).mapIso e)
        ((DeRham.Comparison.CechTotalFunctor.cechTotalFunctor (relativeCechOpenCover U W)).mapIso e)
        (DeRham.Comparison.CechComplexAugmentation.cechTotalAugmentation_naturality (relativeCechOpenCover U W) ⊤
          (fun _ => le_top) e.hom)

end

end OAI.AlgebraicTopology.Cohomology.Singular.SmoothRelativeCechTransport
