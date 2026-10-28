import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! # Normal Pair Recenter -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

/-!
# Genuine local pairs for embedded immersions

A local immersion chart describes the image of one source chart. The embedding
hypothesis supplies an ambient open set whose intersection with the full image
comes entirely from that source chart. After shrinking to a product of balls,
the resulting homeomorphism therefore identifies the actual full image with
the zero normal slice.
-/

open Set Filter
open scoped _root_.Topology _root_.Manifold ContDiff

section TopologicalPairs

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- An actual ambient coordinate neighborhood, with the full image of `f`
identified with the zero normal slice. The fields are constructed below from
a genuine manifold immersion and a topological embedding. -/
structure ImmersionNormalPair (f : M → N) (x : M) where
  radius : ℝ
  radius_pos : 0 < radius
  ambientChart : OpenPartialHomeomorph N (E × F)
  product_subset_target :
    Metric.ball (0 : E) radius ×ˢ Metric.ball (0 : F) radius ⊆ ambientChart.target
  point_mem_source : f x ∈ ambientChart.source
  point_coordinates : ambientChart (f x) = (0, 0)
  range_iff : ∀ y ∈ ambientChart.symm ''
      (Metric.ball (0 : E) radius ×ˢ Metric.ball (0 : F) radius),
    y ∈ Set.range f ↔ (ambientChart y).2 = 0

namespace ImmersionNormalPair

variable {E F} {f : M → N} {x : M} (P : ImmersionNormalPair E F f x)

omit [TopologicalSpace M]

/-- The actual ambient open neighborhood, obtained by pulling back the balls. -/
def neighborhood : Set N :=
  P.ambientChart.symm ''
    (Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius)

theorem isOpen_neighborhood : IsOpen P.neighborhood :=
  P.ambientChart.isOpen_image_symm_of_subset_target
    (Metric.isOpen_ball.prod Metric.isOpen_ball) P.product_subset_target

theorem neighborhood_subset_source : P.neighborhood ⊆ P.ambientChart.source := by
  rintro y ⟨z, hz, rfl⟩
  exact P.ambientChart.map_target (P.product_subset_target hz)

theorem point_mem_neighborhood : f x ∈ P.neighborhood := by
  refine ⟨(0, 0), ⟨Metric.mem_ball_self P.radius_pos, Metric.mem_ball_self P.radius_pos⟩, ?_⟩
  rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]

/-- The genuine homeomorphism onto the product of the two open balls. -/
def homeomorph : P.neighborhood ≃ₜ
    (Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius) :=
  (P.ambientChart.homeomorphOfImageSubsetSource P.neighborhood_subset_source
    (P.ambientChart.image_symm_image_of_subset_target P.product_subset_target)).trans
      (Homeomorph.Set.prod _ _)

@[simp]
theorem homeomorph_apply_val (y : P.neighborhood) :
    ((P.homeomorph y).1.val, (P.homeomorph y).2.val) = P.ambientChart y.val := rfl

theorem homeomorph_point :
    P.homeomorph ⟨f x, P.point_mem_neighborhood⟩ =
      (⟨0, Metric.mem_ball_self P.radius_pos⟩, ⟨0, Metric.mem_ball_self P.radius_pos⟩) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst P.point_coordinates
  · exact congrArg Prod.snd P.point_coordinates

/-- This equivalence uses the full range of `f`, not a restricted source image. -/
theorem mem_range_iff (y : P.neighborhood) :
    y.val ∈ Set.range f ↔ (P.homeomorph y).2.val = 0 :=
  P.range_iff y.val y.property

theorem mem_complement_iff (y : P.neighborhood) :
    y.val ∉ Set.range f ↔ (P.homeomorph y).2.val ≠ 0 :=
  not_congr (P.mem_range_iff y)

/-- Restriction to the subspace in the pair is an actual homeomorphism. -/
def supportHomeomorph : {y : P.neighborhood // y.val ∈ Set.range f} ≃ₜ
    {z : Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius // z.2.val = 0} :=
  P.homeomorph.subtype P.mem_range_iff

/-- The complements in the local pair are also homeomorphic. -/
def complementHomeomorph : {y : P.neighborhood // y.val ∉ Set.range f} ≃ₜ
    {z : Metric.ball (0 : E) P.radius × Metric.ball (0 : F) P.radius // z.2.val ≠ 0} :=
  P.homeomorph.subtype P.mem_complement_iff

/-- The entire image in the ambient neighborhood is precisely the normal
zero plane in the coordinate product. -/
theorem ambientChart_image_support :
    P.ambientChart '' (P.neighborhood ∩ Set.range f) =
      Metric.ball (0 : E) P.radius ×ˢ ({0} : Set F) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyf⟩, rfl⟩
    exact ⟨(P.homeomorph ⟨y, hy⟩).1.property, (P.range_iff y hy).mp hyf⟩
  · rintro ⟨hz1, hz2⟩
    have hprod : z ∈ Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius := by
      refine ⟨hz1, ?_⟩
      rw [show z.2 = 0 from hz2]
      exact Metric.mem_ball_self P.radius_pos
    have ht := P.product_subset_target hprod
    refine ⟨P.ambientChart.symm z, ⟨⟨z, hprod, rfl⟩, ?_⟩, P.ambientChart.right_inv ht⟩
    apply (P.range_iff _ ⟨z, hprod, rfl⟩).mpr
    rw [P.ambientChart.right_inv ht]
    exact hz2

/-- Shrinking both coordinate radii preserves the exact full-image pair. -/
def restrictRadius (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    ImmersionNormalPair E F f x where
  radius := r
  radius_pos := hr
  ambientChart := P.ambientChart
  product_subset_target := fun _ hz => P.product_subset_target
    ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩
  point_mem_source := P.point_mem_source
  point_coordinates := P.point_coordinates
  range_iff := fun y hy => P.range_iff y (by
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩, rfl⟩)

@[simp]
theorem restrictRadius_ambientChart (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    (P.restrictRadius r hr hle).ambientChart = P.ambientChart := rfl

theorem restrictRadius_neighborhood_subset (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius) :
    (P.restrictRadius r hr hle).neighborhood ⊆ P.neighborhood := by
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z, ⟨Metric.ball_subset_ball hle hz.1, Metric.ball_subset_ball hle hz.2⟩, rfl⟩

/-- Such product neighborhoods can be chosen inside every ambient neighborhood
of the base point, while retaining the same actual coordinate map. -/
theorem exists_restrictRadius_subset (U : Set N) (hU : U ∈ 𝓝 (f x)) :
    ∃ (r : ℝ) (hr : 0 < r) (hle : r ≤ P.radius),
      (P.restrictRadius r hr hle).neighborhood ⊆ U := by
  have h0t : (0, 0) ∈ P.ambientChart.target := by
    rw [← P.point_coordinates]
    exact P.ambientChart.map_source P.point_mem_source
  have hinv : P.ambientChart.symm (0, 0) = f x := by
    rw [← P.point_coordinates, P.ambientChart.left_inv P.point_mem_source]
  have hpre : P.ambientChart.symm ⁻¹' U ∈ 𝓝 (0, 0) :=
    (P.ambientChart.continuousAt_symm h0t).preimage_mem_nhds (by rwa [hinv])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min ε P.radius, lt_min hε P.radius_pos, min_le_right _ _, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  apply hball
  apply Metric.ball_subset_ball (min_le_left ε P.radius)
  change z ∈ Metric.ball (0 : E) (min ε P.radius) ×ˢ
    Metric.ball (0 : F) (min ε P.radius) at hz
  simpa only [ball_prod_same] using hz

/-- Cofinality stated directly in terms of genuine normal pairs. -/
theorem exists_subpair (U : Set N) (hU : U ∈ 𝓝 (f x)) :
    ∃ Q : ImmersionNormalPair E F f x,
      Q.ambientChart = P.ambientChart ∧ Q.neighborhood ⊆ U := by
  obtain ⟨r, hr, hle, hsub⟩ := P.exists_restrictRadius_subset U hU
  exact ⟨P.restrictRadius r hr hle, rfl, hsub⟩

end ImmersionNormalPair

variable {E F} {f : M → N} {x : M}

/-- The embedding hypothesis excludes all other source points from a suitable
ambient neighborhood. The local normal form then describes the full image. -/
theorem exists_normalPairRadius (hf : Topology.IsEmbedding f)
    (u : OpenPartialHomeomorph M E) (v : OpenPartialHomeomorph N (E × F))
    (hx : x ∈ u.source) (hmap : u.source ⊆ f ⁻¹' v.source)
    (hnormal : ∀ y ∈ u.source, v (f y) = (u y, 0)) (hcenter : u x = 0) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ v.target ∧
      ∀ y ∈ v.symm '' (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r),
        y ∈ Set.range f ↔ (v y).2 = 0 := by
  obtain ⟨O, hO, hpre⟩ := hf.isInducing.isOpen_iff.mp u.open_source
  have hfxO : f x ∈ O := by
    change x ∈ f ⁻¹' O
    rw [hpre]
    exact hx
  have hzero : v (f x) = (0, 0) := by simpa only [hcenter] using hnormal x hx
  let V : Set (E × F) := v '' (v.source ∩ O) ∩ Prod.fst ⁻¹' u.target
  have hV : IsOpen V :=
    (v.isOpen_image_source_inter hO).inter (u.open_target.preimage continuous_fst)
  have h0 : (0, 0) ∈ V := by
    refine ⟨⟨f x, ⟨hmap hx, hfxO⟩, hzero⟩, ?_⟩
    change (0 : E) ∈ u.target
    simpa only [hcenter] using u.map_source hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0)
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ V := by
    simpa only [ball_prod_same] using hball
  have htarget : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ v.target := by
    intro z hz
    obtain ⟨w, hw, he⟩ := (hprod hz).1
    exact he ▸ v.map_source hw.1
  refine ⟨r, hr, htarget, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hzt : z ∈ v.target := htarget hz
  have hys : v.symm z ∈ v.source := v.map_target hzt
  have hright : v (v.symm z) = z := v.right_inv hzt
  have hyO : v.symm z ∈ O := by
    obtain ⟨w, hw, he⟩ := (hprod hz).1
    rw [← he, v.left_inv hw.1]
    exact hw.2
  have huT : z.1 ∈ u.target := (hprod hz).2
  constructor
  · rintro ⟨a, ha⟩
    have haU : a ∈ u.source := by
      rw [← hpre]
      change f a ∈ O
      rwa [ha]
    rw [← ha, hnormal a haU]
  · intro hzero'
    refine ⟨u.symm z.1, ?_⟩
    have haU : u.symm z.1 ∈ u.source := u.map_target huT
    apply v.injOn (hmap haU) hys
    rw [hnormal _ haU, u.right_inv huT, hright]
    apply Prod.ext
    · rfl
    · rw [hright] at hzero'
      exact hzero'.symm

/-- Package the radius just proved, without assuming any full-image claim. -/
def normalPairOfCharts (hf : Topology.IsEmbedding f)
    (u : OpenPartialHomeomorph M E) (v : OpenPartialHomeomorph N (E × F))
    (hx : x ∈ u.source) (hmap : u.source ⊆ f ⁻¹' v.source)
    (hnormal : ∀ y ∈ u.source, v (f y) = (u y, 0)) (hcenter : u x = 0) :
    ImmersionNormalPair E F f x :=
  let h := exists_normalPairRadius hf u v hx hmap hnormal hcenter
  { radius := Classical.choose h
    radius_pos := (Classical.choose_spec h).1
    ambientChart := v
    product_subset_target := (Classical.choose_spec h).2.1
    point_mem_source := hmap hx
    point_coordinates := by simpa only [hcenter] using hnormal x hx
    range_iff := (Classical.choose_spec h).2.2 }

end TopologicalPairs

variable {𝕜 E G C M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

/-- The source chart supplied by the genuine immersion, centered at `x`. -/
def immersionSourceCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    OpenPartialHomeomorph M E :=
  h.domChart.transHomeomorph (Homeomorph.subRight (h.domChart x))

/-- The genuine immersion chart split into tangential and normal coordinates,
and centered at `(x,0)` in those coordinates. -/
def immersionNormalCoordinates
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    OpenPartialHomeomorph N (E × C) :=
  h.codChart.transHomeomorph
    (h.equiv.symm.toHomeomorph.trans
      ((Homeomorph.subRight (h.domChart x)).prodCongr (Homeomorph.refl C)))

@[simp]
theorem immersionSourceCoordinates_source
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    (immersionSourceCoordinates h).source = h.domChart.source := rfl

@[simp]
theorem immersionNormalCoordinates_source
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    (immersionNormalCoordinates h).source = h.codChart.source := rfl

@[simp]
theorem immersionSourceCoordinates_center
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x) :
    immersionSourceCoordinates h x = 0 := by
  change h.domChart x - h.domChart x = 0
  exact sub_self _

/-- Removing the trivial corner models from the genuine normal-form equation. -/
theorem immersion_codChart_apply
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    {y : M} (hy : y ∈ h.domChart.source) :
    h.codChart (f y) = h.equiv (h.domChart y, 0) := by
  have ht : h.domChart y ∈ (h.domChart.extend 𝓘(𝕜, E)).target := by
    rw [OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe]
    exact ⟨h.domChart y, h.domChart.map_source hy, rfl⟩
  have he := h.writtenInCharts ht
  simpa only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
    id_eq, h.domChart.left_inv hy] using he

/-- In the centered coordinates, the actual immersion is the zero section. -/
theorem immersionNormalCoordinates_apply
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    {y : M} (hy : y ∈ (immersionSourceCoordinates h).source) :
    immersionNormalCoordinates h (f y) = (immersionSourceCoordinates h y, 0) := by
  change ((h.equiv.symm (h.codChart (f y))).1 - h.domChart x,
      (h.equiv.symm (h.codChart (f y))).2) = (h.domChart y - h.domChart x, 0)
  rw [immersion_codChart_apply h hy, h.equiv.symm_apply_apply]

/-- A genuine immersion which is a topological embedding has an actual local
normal pair for its full image. No additional normal form is assumed. -/
def normalPairOfImmersion
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) : ImmersionNormalPair E C f x :=
  normalPairOfCharts hf (immersionSourceCoordinates h) (immersionNormalCoordinates h)
    h.mem_domChart_source h.source_subset_preimage_source
    (fun _ hy => immersionNormalCoordinates_apply h hy) (immersionSourceCoordinates_center h)

@[simp]
theorem normalPairOfImmersion_ambientChart
    (h : Manifold.IsImmersionAtOfComplement C 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) :
    (normalPairOfImmersion h hf).ambientChart = immersionNormalCoordinates h := rfl

/-- The same local pair, using the complement proved to exist by mathlib's
standard `IsImmersionAt` proposition. -/
def immersionNormalPair
    (h : Manifold.IsImmersionAt 𝓘(𝕜, E) 𝓘(𝕜, G) n f x)
    (hf : Topology.IsEmbedding f) : ImmersionNormalPair E h.complement f x :=
  normalPairOfImmersion h.isImmersionAtOfComplement_complement hf

end AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter

namespace AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair

/-!
# Recentering genuine normal pairs

At another point of the image in a verified normal-pair neighborhood, translate
only the tangential coordinate. A sufficiently small positive product ball
stays inside the original verified neighborhood and any requested neighborhood
of the new point. The resulting pair therefore still describes the full image.
-/

open Set Filter
open scoped _root_.Topology

variable {M N E F : Type*} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ImmersionNormalPair E F f x)

/-- Translate only the tangential coordinate to recenter the actual ambient chart. -/
def recenterChart (z : M) : OpenPartialHomeomorph N (E × F) :=
  P.ambientChart.transHomeomorph
    ((Homeomorph.subRight (P.ambientChart (f z)).1).prodCongr (Homeomorph.refl F))

@[simp]
theorem recenterChart_source (z : M) :
    (P.recenterChart z).source = P.ambientChart.source := rfl

@[simp]
theorem recenterChart_apply (z : M) (y : N) :
    P.recenterChart z y =
      ((P.ambientChart y).1 - (P.ambientChart (f z)).1, (P.ambientChart y).2) := rfl

@[simp]
theorem recenterChart_symm_apply (z : M) (w : E × F) :
    (P.recenterChart z).symm w =
      P.ambientChart.symm (w.1 + (P.ambientChart (f z)).1, w.2) := rfl

/-- In particular, normal coordinates are unchanged everywhere, not merely at the center. -/
@[simp]
theorem recenterChart_normalCoordinate (z : M) (y : N) :
    (P.recenterChart z y).2 = (P.ambientChart y).2 := rfl

theorem recenterChart_point_mem_source (z : M) (hz : f z ∈ P.neighborhood) :
    f z ∈ (P.recenterChart z).source :=
  P.neighborhood_subset_source hz

/-- The full-image property proves that the new image point has zero normal coordinate. -/
@[simp]
theorem recenterChart_point (z : M) (hz : f z ∈ P.neighborhood) :
    P.recenterChart z (f z) = (0, 0) := by
  have hn : (P.ambientChart (f z)).2 = 0 :=
    (P.range_iff (f z) hz).mp ⟨z, rfl⟩
  simp only [recenterChart_apply, sub_self, hn]

theorem recenterChart_zero_mem_target (z : M) (hz : f z ∈ P.neighborhood) :
    (0, 0) ∈ (P.recenterChart z).target := by
  rw [← P.recenterChart_point z hz]
  exact (P.recenterChart z).map_source (P.recenterChart_point_mem_source z hz)

@[simp]
theorem recenterChart_symm_zero (z : M) (hz : f z ∈ P.neighborhood) :
    (P.recenterChart z).symm (0, 0) = f z := by
  rw [← P.recenterChart_point z hz,
    (P.recenterChart z).left_inv (P.recenterChart_point_mem_source z hz)]

/-- A positive product ball in the recentered chart can be chosen inside the
original verified pair and any requested neighborhood of the new point. -/
theorem exists_recenterRadius (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ (P.recenterChart z).target ∧
      (P.recenterChart z).symm ''
        (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r) ⊆ P.neighborhood ∩ U := by
  have ht := P.recenterChart_zero_mem_target z hz
  have hn : P.neighborhood ∩ U ∈ 𝓝 (f z) :=
    inter_mem (P.isOpen_neighborhood.mem_nhds hz) hU
  have hp : (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) ∈ 𝓝 (0, 0) :=
    ((P.recenterChart z).continuousAt_symm ht).preimage_mem_nhds
      (by rwa [P.recenterChart_symm_zero z hz])
  have hv : (P.recenterChart z).target ∩
      (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) ∈ 𝓝 (0, 0) :=
    inter_mem ((P.recenterChart z).open_target.mem_nhds ht) hp
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hv
  have hprod : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆
      (P.recenterChart z).target ∩
        (P.recenterChart z).symm ⁻¹' (P.neighborhood ∩ U) := by
    simpa only [ball_prod_same] using hball
  refine ⟨r, hr, fun w hw => (hprod hw).1, ?_⟩
  rintro y ⟨w, hw, rfl⟩
  exact (hprod hw).2

/-- A genuine normal pair centered at any image point in the original pair,
with its entire verified neighborhood contained in the requested overlap. -/
def recenterWithin (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) : ImmersionNormalPair E F f z :=
  let h := P.exists_recenterRadius z hz U hU
  { radius := Classical.choose h
    radius_pos := (Classical.choose_spec h).1
    ambientChart := P.recenterChart z
    product_subset_target := (Classical.choose_spec h).2.1
    point_mem_source := P.recenterChart_point_mem_source z hz
    point_coordinates := P.recenterChart_point z hz
    range_iff := fun y hy => P.range_iff y ((Classical.choose_spec h).2.2 hy).1 }

@[simp]
theorem recenterWithin_ambientChart (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).ambientChart = P.recenterChart z := rfl

@[simp]
theorem recenterWithin_ambientChart_apply (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (y : N) :
    (P.recenterWithin z hz U hU).ambientChart y =
      ((P.ambientChart y).1 - (P.ambientChart (f z)).1, (P.ambientChart y).2) := rfl

@[simp]
theorem recenterWithin_normalCoordinate (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (y : N) :
    ((P.recenterWithin z hz U hU).ambientChart y).2 = (P.ambientChart y).2 := rfl

/-- The new normal slice is the original normal fiber over the new tangential coordinate. -/
@[simp]
theorem recenterWithin_normalSlice (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) (v : F) :
    (P.recenterWithin z hz U hU).ambientChart.symm (0, v) =
      P.ambientChart.symm ((P.ambientChart (f z)).1, v) := by
  simp only [recenterWithin_ambientChart, recenterChart_symm_apply, zero_add]

theorem recenterWithin_neighborhood_subset (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    (P.recenterWithin z hz U hU).neighborhood ⊆ P.neighborhood ∩ U :=
  (Classical.choose_spec (P.exists_recenterRadius z hz U hU)).2.2

/-- An existence version records both the exact translated chart and the overlap containment. -/
theorem exists_recentered_subpair (z : M) (hz : f z ∈ P.neighborhood)
    (U : Set N) (hU : U ∈ 𝓝 (f z)) :
    ∃ Q : ImmersionNormalPair E F f z,
      Q.ambientChart = P.recenterChart z ∧ Q.neighborhood ⊆ P.neighborhood ∩ U :=
  ⟨P.recenterWithin z hz U hU, rfl, P.recenterWithin_neighborhood_subset z hz U hU⟩

end AlgebraicGeometry.ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair

end

end OAI
