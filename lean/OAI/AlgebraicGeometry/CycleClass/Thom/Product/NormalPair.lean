import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Product

/-! # Normal Pair -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions

noncomputable section

/-! A genuine normal pair for the product immersion, constructed from two
actual normal pairs and complex-linear coordinates on the combined normal
space. The radius is chosen inside their actual product neighborhood. -/

open _root_.CategoryTheory
open Set Filter
open scoped _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem centeredChart_exists_radius {N E F : Type} [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (v : OpenPartialHomeomorph N (E × F)) {z : N}
    (hz : z ∈ v.source) (hc : v z = (0, 0))
    {U : Set N} (hU : IsOpen U) (hzU : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆ v.target ∧
      v.symm '' (Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r) ⊆ U := by
  have hO : IsOpen (v '' (v.source ∩ U)) := v.isOpen_image_source_inter hU
  have h0 : (0, 0) ∈ v '' (v.source ∩ U) := ⟨z, ⟨hz, hzU⟩, hc⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0)
  have hb : Metric.ball (0 : E) r ×ˢ Metric.ball (0 : F) r ⊆
      v '' (v.source ∩ U) := by
    simpa only [ball_prod_same] using hball
  refine ⟨r, hr, ?_, ?_⟩
  · intro w hw
    obtain ⟨a, ha, rfl⟩ := hb hw
    exact v.map_source ha.1
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hb hw
    simpa only [v.left_inv ha.1] using ha.2

variable {M N M' N' E F : Type} [TopologicalSpace N] [TopologicalSpace N']
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {p q : ℕ} {u : M → N} {v : M' → N'} {x : M} {y : M'}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
  (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair F (Fin q → ℂ) v y)
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

def productNormalCoordinates :
    ((E × (Fin p → ℂ)) × (F × (Fin q → ℂ))) ≃L[ℂ]
      ((E × F) × (Fin (p + q) → ℂ)) :=
  (ContinuousLinearEquiv.prodProdProdComm ℂ E (Fin p → ℂ) F (Fin q → ℂ)).trans
    ((ContinuousLinearEquiv.refl ℂ (E × F)).prodCongr e)

def productNormalChart : OpenPartialHomeomorph (N × N') ((E × F) × (Fin (p + q) → ℂ)) :=
  (P.ambientChart.prod Q.ambientChart).transHomeomorph
    (productNormalCoordinates (E := E) (F := F) e).toHomeomorph

theorem productNormalChart_apply (z : N × N') :
    productNormalChart P Q e z =
      (((P.ambientChart z.1).1, (Q.ambientChart z.2).1),
        e ((P.ambientChart z.1).2, (Q.ambientChart z.2).2)) := rfl

theorem productNormalChart_point : productNormalChart P Q e (u x, v y) = (0, 0) := by
  rw [productNormalChart_apply, P.point_coordinates, Q.point_coordinates]
  change ((0, 0), e 0) = (0, 0)
  rw [map_zero]
  rfl

theorem productNormalChart_point_source : (u x, v y) ∈ (productNormalChart P Q e).source :=
  ⟨P.point_mem_source, Q.point_mem_source⟩

theorem productNormalChart_exists_radius :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : E × F) r ×ˢ Metric.ball (0 : Fin (p + q) → ℂ) r ⊆
        (productNormalChart P Q e).target ∧
      (productNormalChart P Q e).symm ''
        (Metric.ball (0 : E × F) r ×ˢ Metric.ball (0 : Fin (p + q) → ℂ) r) ⊆
          P.neighborhood ×ˢ Q.neighborhood :=
  centeredChart_exists_radius (N := N × N') (E := E × F) (F := Fin (p + q) → ℂ)
    (z := (u x, v y)) (U := P.neighborhood ×ˢ Q.neighborhood) (productNormalChart P Q e)
    (productNormalChart_point_source P Q e) (productNormalChart_point P Q e)
    (P.isOpen_neighborhood.prod Q.isOpen_neighborhood)
    ⟨P.point_mem_neighborhood, Q.point_mem_neighborhood⟩

theorem productNormalChart_range_iff (z : N × N')
    (hz : z ∈ P.neighborhood ×ˢ Q.neighborhood) :
    z ∈ Set.range (Prod.map u v) ↔ (productNormalChart P Q e z).2 = 0 := by
  rw [productNormalChart_apply]
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    have ha : z.1 ∈ Set.range u := ⟨a, congrArg Prod.fst hab⟩
    have hb : z.2 ∈ Set.range v := ⟨b, congrArg Prod.snd hab⟩
    rw [(P.range_iff _ hz.1).mp ha, (Q.range_iff _ hz.2).mp hb]
    exact map_zero e
  · intro h
    have he : ((P.ambientChart z.1).2, (Q.ambientChart z.2).2) = 0 :=
      e.injective (h.trans (map_zero e).symm)
    obtain ⟨a, ha⟩ := (P.range_iff _ hz.1).mpr (congrArg Prod.fst he)
    obtain ⟨b, hb⟩ := (Q.range_iff _ hz.2).mpr (congrArg Prod.snd he)
    exact ⟨(a, b), Prod.ext ha hb⟩

/-- A genuine normal pair for the full range of the product map. -/
def productNormalPair :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (E × F) (Fin (p + q) → ℂ) (Prod.map u v) (x, y) where
  radius := Classical.choose (productNormalChart_exists_radius P Q e)
  radius_pos := (Classical.choose_spec (productNormalChart_exists_radius P Q e)).1
  ambientChart := productNormalChart P Q e
  product_subset_target := (Classical.choose_spec (productNormalChart_exists_radius P Q e)).2.1
  point_mem_source := productNormalChart_point_source P Q e
  point_coordinates := productNormalChart_point P Q e
  range_iff := fun z hz => productNormalChart_range_iff P Q e z
    ((Classical.choose_spec (productNormalChart_exists_radius P Q e)).2.2 hz)

theorem productNormalPair_neighborhood_subset :
    (productNormalPair P Q e).neighborhood ⊆ P.neighborhood ×ˢ Q.neighborhood :=
  (Classical.choose_spec (productNormalChart_exists_radius P Q e)).2.2

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions
