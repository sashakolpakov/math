import OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair

/-! # Normal Pair -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalPair.BundleCycles

noncomputable section

/-! A normal pair for a product with an unrestricted smooth factor.
Its normal coordinate is exactly the original normal coordinate after
the actual second projection. No normal class comparison is assumed. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Thom.Product.NormalPair.Constructions

variable {M N B E F : Type} [TopologicalSpace N] [TopologicalSpace B]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {u : M → N} {x : M} {p : ℕ}
    (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E (Fin p → ℂ) u x)
    (c : OpenPartialHomeomorph B F) (b : B) (hb : b ∈ c.source) (hc : c b = 0)

def projectionNormalCoordinates : (F × (E × (Fin p → ℂ))) ≃L[ℂ] ((F × E) × (Fin p → ℂ)) :=
  (LinearIsometryEquiv.prodAssoc ℂ F E (Fin p → ℂ)).symm.toContinuousLinearEquiv

def projectionNormalChart : OpenPartialHomeomorph (B × N) ((F × E) × (Fin p → ℂ)) :=
  (c.prod P.ambientChart).transHomeomorph (projectionNormalCoordinates (E := E) (F := F) (p := p)).toHomeomorph

theorem projectionNormalChart_apply (z : B × N) :
    projectionNormalChart P c z = ((c z.1, (P.ambientChart z.2).1), (P.ambientChart z.2).2) := rfl

include hb hc in
theorem projectionNormalChart_radius :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (0 : F × E) r ×ˢ Metric.ball (0 : Fin p → ℂ) r ⊆
        (projectionNormalChart P c).target ∧
      (projectionNormalChart P c).symm ''
        (Metric.ball (0 : F × E) r ×ˢ Metric.ball (0 : Fin p → ℂ) r) ⊆
          c.source ×ˢ P.neighborhood := by
  apply CycleClass.Thom.Product.NormalPair.Constructions.centeredChart_exists_radius (N := B × N) (E := F × E) (F := Fin p → ℂ)
    (z := (b, u x)) (U := c.source ×ˢ P.neighborhood) (projectionNormalChart P c)
  · exact ⟨hb, P.point_mem_source⟩
  · rw [projectionNormalChart_apply, hc, P.point_coordinates]
    rfl
  · exact c.open_source.prod P.isOpen_neighborhood
  · exact ⟨hb, P.point_mem_neighborhood⟩

def projectionNormalPair :
    ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (F × E) (Fin p → ℂ) (Prod.map id u) (b, x) where
  radius := Classical.choose (projectionNormalChart_radius P c b hb hc)
  radius_pos := (Classical.choose_spec (projectionNormalChart_radius P c b hb hc)).1
  ambientChart := projectionNormalChart P c
  product_subset_target := (Classical.choose_spec (projectionNormalChart_radius P c b hb hc)).2.1
  point_mem_source := ⟨hb, P.point_mem_source⟩
  point_coordinates := by
    change projectionNormalChart P c (b, u x) = (0, 0)
    rw [projectionNormalChart_apply, hc, P.point_coordinates]
    rfl
  range_iff := fun z hz => by
    have hz' := (Classical.choose_spec (projectionNormalChart_radius P c b hb hc)).2.2 hz
    change z ∈ Set.range (Prod.map id u) ↔ (P.ambientChart z.2).2 = 0
    rw [← P.range_iff z.2 hz'.2]
    constructor
    · rintro ⟨⟨a, m⟩, hm⟩
      exact ⟨m, congrArg Prod.snd hm⟩
    · rintro ⟨m, hm⟩
      exact ⟨(z.1, m), Prod.ext rfl hm⟩

theorem projectionNormalPair_neighborhood :
    (projectionNormalPair P c b hb hc).neighborhood ⊆ c.source ×ˢ P.neighborhood :=
  (Classical.choose_spec (projectionNormalChart_radius P c b hb hc)).2.2

theorem projectionNormalPair_coordinate (z : (projectionNormalPair P c b hb hc).neighborhood) :
    (projectionNormalPair P c b hb hc).normalCoordinate z = (P.ambientChart z.val.2).2 := rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projection.NormalPair.BundleCycles
