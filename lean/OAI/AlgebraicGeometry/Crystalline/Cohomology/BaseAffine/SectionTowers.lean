import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars

/-! # Section Towers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers

noncomputable section

/-! # Actual affine section scalar towers over an arbitrary commutative base -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def affineScheme : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

theorem sectionBaseMap (U : (Spec (CommRingCat.of A)).Opens) :
    AlgebraicForms.AlgebraicDeRham.sectionBaseMap R (affineScheme R A) U =
      (AlgebraicForms.AlgebraicDeRham.sectionBaseMap A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) U).comp (algebraMap R A) := by
  have h := NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange.sectionBaseMap_comp (algebraMap R A) (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) U
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    ((𝟙 (Spec (CommRingCat.of A))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤ U le_top).hom = _ at h
  rw [Category.id_comp] at h
  exact h

@[instance_reducible]
def coordinateAlgebra (U : (Spec (CommRingCat.of A)).Opens) : Algebra A Γ(Spec (CommRingCat.of A), U) :=
  AlgebraicForms.AlgebraicDeRham.sectionAlgebra A (NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars.base A) U

theorem tower (U : (Spec (CommRingCat.of A)).Opens) :
    letI : Algebra R Γ(Spec (CommRingCat.of A), U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (affineScheme R A) U
    letI : Algebra A Γ(Spec (CommRingCat.of A), U) := coordinateAlgebra A U
    IsScalarTower R A Γ(Spec (CommRingCat.of A), U) := by
  let : Algebra R Γ(Spec (CommRingCat.of A), U) := AlgebraicForms.AlgebraicDeRham.sectionAlgebra R (affineScheme R A) U
  let : Algebra A Γ(Spec (CommRingCat.of A), U) := coordinateAlgebra A U
  exact IsScalarTower.of_algebraMap_eq (fun r => DFunLike.congr_fun (sectionBaseMap R A U) r)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BaseAffine.SectionTowers.BaseAffineSectionTowers
