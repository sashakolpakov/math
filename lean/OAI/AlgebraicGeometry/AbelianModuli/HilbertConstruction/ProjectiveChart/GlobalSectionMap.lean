import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.MapRecognition

/-! # Global Section Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.GlobalSectionMap

noncomputable section

/-! The canonical homogeneous-localization map into the global functions
of a basic open recovers its actual inclusion into projective spectrum. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A)

def projectiveChartGlobalSectionMap :
    HomogeneousLocalization.Away 𝒜 f →+* Γ((Proj.basicOpen 𝒜 f).toScheme, ⊤) :=
  (Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv).hom

theorem projectiveChartGlobalSectionMap_spec {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Proj.basicOpen 𝒜 f).toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (projectiveChartGlobalSectionMap 𝒜 f)) =
        (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom := by
  change (Proj.basicOpen 𝒜 f).toScheme.toSpecΓ ≫
    Spec.map (Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv) =
      ((Proj.basicOpen 𝒜 f).toScheme.toSpecΓ ≫ Spec.map (Proj.basicOpen 𝒜 f).topIso.inv) ≫
        Spec.map (Proj.awayToSection 𝒜 f)
  rw [Spec.map_comp, Category.assoc]

theorem projectiveChartGlobalSectionMap_awayι {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ((Proj.basicOpen 𝒜 f).toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (projectiveChartGlobalSectionMap 𝒜 f))) ≫ Proj.awayι 𝒜 f hf hd =
        (Proj.basicOpen 𝒜 f).ι := by
  rw [projectiveChartGlobalSectionMap_spec]
  change (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom ≫
    ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv ≫ (Proj.basicOpen 𝒜 f).ι) = _
  rw [Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.GlobalSectionMap
