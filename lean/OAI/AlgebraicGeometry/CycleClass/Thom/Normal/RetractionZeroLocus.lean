import OAI.AlgebraicGeometry.CycleClass.Thom.RetractionSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Retraction Zero Locus -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionZeroLocus.Constructions

noncomputable section

/-! The actual concatenated normal equations vanish exactly on the
ambient image of the source zero locus. Their relative support is that
same image, with no change to the represented closed subset. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.IntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {p d : ℕ}
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin p → ℂ) f x)
  (hf : Topology.IsEmbedding f)

theorem sourceInclusion_range :
    Set.range (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) =
      Subtype.val ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.val, rfl⟩
  · rintro ⟨z, hzy⟩
    have hz : f z ∈ P.neighborhood := hzy.symm ▸ y.property
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩

theorem sourceInclusion_complement :
    P.relativeComplement = (Set.range (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf))ᶜ := by
  rw [sourceInclusion_range]
  rfl

variable {q : ℕ}
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) ⟶ TopCat.of (Fin q → ℂ))
  (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ))

theorem equations_zero_iff (y : P.neighborhood) :
    IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf ≫ g) e y = 0 ↔
      y ∈ (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) '' (g ⁻¹' {0}) := by
  have he : IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf ≫ g) e y = 0 ↔
      P.normalCoordinate y = 0 ∧ g (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf y) = 0 := by
    change e (P.normalCoordinate y, g (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf y)) = 0 ↔ _
    rw [map_eq_zero_iff e e.injective]
    exact Prod.mk_eq_zero
  rw [he]
  constructor
  · rintro ⟨hn, hg⟩
    have hy : y ∈ Set.range (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) := by
      rw [sourceInclusion_range]
      exact (P.mem_range_iff y).mpr hn
    obtain ⟨z, rfl⟩ := hy
    rw [HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairSourceRetraction_left_inverse] at hg
    exact ⟨z, hg, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(P.mem_range_iff _).mp ⟨z.val, rfl⟩, ?_⟩
    rw [HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions.normalPairSourceRetraction_left_inverse]
    exact hz

theorem equations_support_complement :
    P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) ⁻¹' (g ⁻¹' {0}ᶜ) =
      ((HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf) '' (g ⁻¹' {0}))ᶜ := by
  rw [sourceInclusion_complement]
  have h := RetractionSupport.Constructions.image_complement (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P hf)
    (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P hf) (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P hf) (g ⁻¹' {0}ᶜ)
  simpa only [Set.preimage_compl, compl_compl] using h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionZeroLocus.Constructions
