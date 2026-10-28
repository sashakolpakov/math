import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.MapOverBase

/-! # Graded Projective Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedProjectiveIsomorphism

noncomputable section

/-! Inverse graded ring maps induce actual inverse maps of projective schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R B)
variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

theorem gradedMap_irrelevant_of_inverse (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (h : f.comp g = GradedRingHom.id ℬ) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro d hd b hb
  have hg : g b ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (g.map_mem hb)
  have hf := Ideal.mem_map_of_mem f.toRingHom hg
  have he : f (g b) = b := DFunLike.congr_fun h b
  exact he ▸ hf

def gradedProjectiveIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hfg : f.comp g = GradedRingHom.id ℬ) (hgf : g.comp f = GradedRingHom.id 𝒜) :
    Proj 𝒜 ≅ Proj ℬ where
  hom := Proj.map g (gradedMap_irrelevant_of_inverse ℬ 𝒜 g f hgf)
  inv := Proj.map f (gradedMap_irrelevant_of_inverse 𝒜 ℬ f g hfg)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [hgf, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [hfg, Proj.map_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedProjectiveIsomorphism
