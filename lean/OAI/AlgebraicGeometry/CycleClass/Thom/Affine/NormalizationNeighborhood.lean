import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap
import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry

/-! # Normalization Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions

noncomputable section

/-! At every parent-cycle point in the normalization base, a genuine
smaller affine base retains a nonempty actual normalization source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)

 theorem normalizationBase_nonempty (B : V.carrier.Opens) (x : V.carrier)
    (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B) :
    Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B) := by
  obtain ⟨z, hz⟩ := Normalization.Scheme.Constructions.normalizationMap_surjective D.scheme (IntersectionGeometry.supportPreimage D.val x hxD)
  have he : (Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left z = x :=
    (congrArg D.inclusion hz).trans (IntersectionGeometry.supportPreimage_spec D.val x hxD)
  exact ⟨⟨z, (congrArg (fun y : V.carrier => y ∈ B) he).mpr hxB⟩⟩

 theorem exists_affine_normalization_neighborhood (B : V.carrier.Opens) (x : V.carrier)
    (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B) (hxN : x ∈ Normalization.AmbientMap.Constructions.ambientOpen V D.val) :
    ∃ C : V.carrier.Opens, IsAffineOpen C ∧ x ∈ C ∧ C ≤ B ∧ C ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val ∧
      Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ C) := by
  obtain ⟨C, hC, hxC, hCB⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ B ⊓ Normalization.AmbientMap.Constructions.ambientOpen V D.val from ⟨hxB, hxN⟩)
  exact ⟨C, hC, hxC, (fun _ hy => (hCB hy).1), (fun _ hy => (hCB hy).2),
    normalizationBase_nonempty D C x hxD hxC⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.NormalizationNeighborhood.Constructions
