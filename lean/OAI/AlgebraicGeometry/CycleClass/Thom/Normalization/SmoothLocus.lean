import OAI.AlgebraicGeometry.CycleClass.Thom.DVRStalkSmooth
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Height
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum

/-! # Smooth Locus -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions

/-! The constructed finite normalization is smooth at all divisor points.
Its actual nonsmooth locus has intrinsic codimension at least two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Height.Constructions.Local OAI.AlgebraicGeometry.CycleClass.Thom.DVRStalkSmooth.Constructions

variable (X : Scheme) [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem normalization_divisorPoint_smooth (y : Normalization.Scheme.Constructions.normalization X) (hy : coheight y = 1) :
    letI : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
    y ∈ (Normalization.Scheme.Constructions.normalizationMap X ≫ f).smoothLocus := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  let : IsDiscreteValuationRing ((Normalization.Scheme.Constructions.normalization X).presheaf.stalk y) :=
    Normalization.Scheme.Constructions.normalization_stalk_isDVR X f y hy
  exact DVRStalkSmooth.Constructions.mem_smoothLocus_of_stalk_dvr (Normalization.Scheme.Constructions.normalizationMap X ≫ f) y

theorem normalization_singular_coheight_gt_one (y : Normalization.Scheme.Constructions.normalization X)
    (hy : letI : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
      y ∈ Geometric.SingularLocus.singularLocus (Normalization.Scheme.Constructions.normalizationMap X ≫ f)) : 1 < coheight y := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  have hpos := Geometric.SingularLocus.coheight_pos_of_mem_singularLocus (Normalization.Scheme.Constructions.normalizationMap X ≫ f) y hy
  have hne : coheight y ≠ 1 := fun h => hy (normalization_divisorPoint_smooth X f y h)
  exact lt_of_le_of_ne (Order.one_le_iff_pos.mpr hpos) hne.symm

/-- The image in the original support retains intrinsic codimension at least two. -/
theorem normalization_singular_image_coheight_gt_one (y : Normalization.Scheme.Constructions.normalization X)
    (hy : letI : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
      y ∈ Geometric.SingularLocus.singularLocus (Normalization.Scheme.Constructions.normalizationMap X ≫ f)) :
    1 < coheight (Normalization.Scheme.Constructions.normalizationMap X y) := by
  rw [Height.Constructions.Local.normalizationMap_coheight X f y]
  exact normalization_singular_coheight_gt_one X f y hy

end AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open

/-! Removing the actual image of the normalization's nonsmooth locus
gives a finite map from a smooth open subscheme. All divisor points of
the original support remain in this open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions

variable (X : Scheme) [IsIntegral X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

def normalizationSingularImage : Closeds X := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  exact ⟨Normalization.Scheme.Constructions.normalizationMap X '' Geometric.SingularLocus.singularLocus (Normalization.Scheme.Constructions.normalizationMap X ≫ f),
    (Normalization.Scheme.Constructions.normalizationMap X).isClosedMap _ (Geometric.SingularLocus.isClosed_singularLocus _)⟩

def normalizationSmoothBase : X.Opens := (normalizationSingularImage X f).compl

theorem normalizationSmoothBase_divisorPoint (x : X) (hx : coheight x = 1) :
    x ∈ normalizationSmoothBase X f := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  rintro ⟨y, hy, he⟩
  have h := normalization_singular_image_coheight_gt_one X f y hy
  rw [he, hx] at h
  exact lt_irrefl _ h

theorem normalizationSmoothBase_genericPoint : genericPoint X ∈ normalizationSmoothBase X f := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  rintro ⟨y, hy, he⟩
  have h := normalization_singular_image_coheight_gt_one X f y hy
  have hg : coheight (genericPoint X) = 0 := by
    apply coheight_eq_zero.mpr
    intro z _
    exact Scheme.le_iff_specializes.mpr (genericPoint_specializes z)
  rw [he, hg] at h
  exact (not_lt_of_ge (show (0 : ℕ∞) ≤ 1 from zero_le)) h

theorem normalizationSmoothBase_preimage_smooth :
    Smooth ((Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ normalizationSmoothBase X f).ι ≫
      (Normalization.Scheme.Constructions.normalizationMap X ≫ f)) := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  let g := Normalization.Scheme.Constructions.normalizationMap X ≫ f
  have hle : Normalization.Scheme.Constructions.normalizationMap X ⁻¹ᵁ normalizationSmoothBase X f ≤ g.smoothLocus := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  let : Smooth (g.smoothLocus.ι ≫ g) := Geometric.SmoothStratum.smoothStratumToBase_isSmooth g
  rw [← (Normalization.Scheme.Constructions.normalization X).homOfLE_ι hle, Category.assoc]
  infer_instance

theorem normalizationSmoothBase_map_finite :
    IsFinite (Normalization.Scheme.Constructions.normalizationMap X ∣_ normalizationSmoothBase X f) := by
  let : IsFinite (Normalization.Scheme.Constructions.normalizationMap X) := Normalization.Scheme.Constructions.normalizationMap_isFinite X f
  infer_instance

end AlgebraicGeometry.CycleClass.Thom.Normalization.SmoothLocus.Constructions.Open

end

end OAI
