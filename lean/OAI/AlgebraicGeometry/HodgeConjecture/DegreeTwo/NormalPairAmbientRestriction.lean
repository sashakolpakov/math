import OAI.AlgebraicTopology.Duality.Poincare.ImmersionLocalPurity

/-! # Normal Pair Ambient Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions

noncomputable section

/-!
# DegreeTwo: restrict a genuine normal pair to an ambient open

If its whole normal neighborhood lies in the open, the pair restricts
with exactly the same coordinates and the full restricted support image.
-/

open _root_.TopologicalSpace

variable {M N E F : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (U : Opens N) (hPU : P.neighborhood ⊆ U)

def supportInOpen : {m : M // f m ∈ U} → U := fun m => ⟨f m.val, m.property⟩

theorem supportInOpen_range (y : U) :
    y ∈ Set.range (supportInOpen (f := f) U) ↔ y.val ∈ Set.range f := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m.val, rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨m, hm ▸ y.property⟩, Subtype.ext hm⟩

/-- Restrict a genuine normal pair to an ambient open containing its
whole geometric neighborhood, using the actual restricted support. -/
def normalPairRestrictAmbient : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F (supportInOpen (f := f) U)
    ⟨x, hPU P.point_mem_neighborhood⟩ := by
  let hxU := hPU P.point_mem_neighborhood
  let hU : Nonempty U := ⟨⟨f x, hxU⟩⟩
  let q := P.ambientChart.subtypeRestr hU
  have htarget : Metric.ball (0 : E) P.radius ×ˢ Metric.ball (0 : F) P.radius ⊆ q.target := by
    intro z hz
    have hzt := P.product_subset_target hz
    have hu : P.ambientChart.symm z ∈ U := hPU ⟨z, hz, rfl⟩
    have h := P.ambientChart.map_subtype_source hU
      (x := ⟨P.ambientChart.symm z, hu⟩) (P.ambientChart.map_target hzt)
    change P.ambientChart (P.ambientChart.symm z) ∈ q.target at h
    rwa [P.ambientChart.right_inv hzt] at h
  refine {
    radius := P.radius
    radius_pos := P.radius_pos
    ambientChart := q
    product_subset_target := htarget
    point_mem_source := ?_
    point_coordinates := P.point_coordinates
    range_iff := ?_ }
  · rw [P.ambientChart.subtypeRestr_source]
    exact P.point_mem_source
  · intro y hy
    have hyP : y.val ∈ P.neighborhood := by
      obtain ⟨z, hz, rfl⟩ := hy
      refine ⟨z, hz, ?_⟩
      exact (P.ambientChart.subtypeRestr_symm_apply hU (htarget hz)).symm
    exact (supportInOpen_range U y).trans (P.range_iff y.val hyP)

theorem normalPairRestrictAmbient_coordinate
    (y : (normalPairRestrictAmbient P U hPU).neighborhood) :
    (normalPairRestrictAmbient P U hPU).normalCoordinate y =
      (P.ambientChart y.val.val).2 := rfl

/-- The restricted geometric neighborhood lies over the original one. -/
theorem normalPairRestrictAmbient_neighborhood
    (y : (normalPairRestrictAmbient P U hPU).neighborhood) :
    y.val.val ∈ P.neighborhood := by
  obtain ⟨z, hz, he⟩ := y.property
  refine ⟨z, hz, ?_⟩
  have hzt := (normalPairRestrictAmbient P U hPU).product_subset_target hz
  have hi := P.ambientChart.subtypeRestr_symm_apply
    (show Nonempty U from ⟨⟨f x, hPU P.point_mem_neighborhood⟩⟩) hzt
  exact hi.symm.trans (congrArg Subtype.val he)

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairAmbientRestriction.Constructions
