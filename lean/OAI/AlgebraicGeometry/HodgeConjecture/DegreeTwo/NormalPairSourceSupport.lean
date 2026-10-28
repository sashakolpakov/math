import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairProductSupport
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairCompactSupport

/-! # Normal Pair Source Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions

noncomputable section

/-! Normal-pair Gysin supports are the literal images of compact source supports. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {c d : ℕ}
variable {f : M → N} {x : M}
variable (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) (Fin c → ℂ) f x) (hf : Topology.IsEmbedding f)

def normalPairSourceInclusionMap : TopCat.of (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) ⟶ TopCat.of P.neighborhood :=
  TopCat.ofHom ⟨NormalPairProductSupport.Constructions.normalPairSourceToNeighborhood P hf,
    (hf.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem normalPairSourceInclusion_coordinates (y : NormalPairProductSupport.Constructions.normalPairSourceOpen P hf) :
    NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P (normalPairSourceInclusionMap P hf y) =
      (NormalPairProductSupport.Constructions.normalPairNormalOrigin P, NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf y) := by
  exact Prod.ext (NormalPairProductSupport.Constructions.normalPairSource_normal_zero P hf y) rfl

theorem normalPairSourceCompactSupport_image (K : Compacts (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)) :
    NormalPairCompactSupport.Constructions.normalPairCompactSupport P (Compacts.equiv (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf) K) =
      OpenEmbeddingExtension.Constructions.embeddingCompactImage (normalPairSourceInclusionMap P hf) K := by
  apply (Compacts.equiv (NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P)).injective
  rw [NormalPairCompactSupport.Constructions.normalPairCompactSupport_image]
  apply Compacts.ext
  change ({NormalPairProductSupport.Constructions.normalPairNormalOrigin P} ×ˢ
    (NormalPairProductSupport.Constructions.normalPairSourceHomeomorph P hf '' (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)))) =
    NormalPairProductSupport.Constructions.normalPairFirstHomeomorph P '' (normalPairSourceInclusionMap P hf '' (K : Set (NormalPairProductSupport.Constructions.normalPairSourceOpen P hf)))
  ext z
  constructor
  · rintro ⟨hz, y, hy, hyz⟩
    refine ⟨normalPairSourceInclusionMap P hf y, ⟨y,hy,rfl⟩, ?_⟩
    exact (normalPairSourceInclusion_coordinates P hf y).trans (Prod.ext hz.symm hyz)
  · rintro ⟨w,⟨y,hy,rfl⟩,rfl⟩
    rw [normalPairSourceInclusion_coordinates]
    exact ⟨rfl,y,hy,rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions
