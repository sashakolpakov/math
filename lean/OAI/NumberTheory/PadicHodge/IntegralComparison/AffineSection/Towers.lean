import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ModuleScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

/-! # Towers -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Towers

noncomputable section

/-!
# IntegralComparison: native affine section algebras retain the coordinate-ring scalar tower
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k C : Type u) [Field k] [CommRing C] [Algebra k C]

theorem sectionBaseMap (U : (Spec (CommRingCat.of C)).Opens) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k (Crystalline.Presentation.affineScheme k C) U =
      (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap C (Affine.ModuleScalars.base C) U).comp (algebraMap k C) := by
  have h := SectionBaseChange.sectionBaseMap_comp (algebraMap k C) (Affine.ModuleScalars.base C) U
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    ((𝟙 (Spec (CommRingCat.of C))) ≫ Spec.map (CommRingCat.ofHom (algebraMap k C))).appLE ⊤ U le_top).hom = _ at h
  rw [Category.id_comp] at h
  exact h

@[instance_reducible]
def coordinateAlgebra (U : (Spec (CommRingCat.of C)).Opens) : Algebra C Γ(Spec (CommRingCat.of C), U) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra C (Affine.ModuleScalars.base C) U

theorem tower (U : (Spec (CommRingCat.of C)).Opens) :
    letI : Algebra k Γ(Spec (CommRingCat.of C), U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k (Crystalline.Presentation.affineScheme k C) U
    letI : Algebra C Γ(Spec (CommRingCat.of C), U) := coordinateAlgebra C U
    IsScalarTower k C Γ(Spec (CommRingCat.of C), U) := by
  let : Algebra k Γ(Spec (CommRingCat.of C), U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra k (Crystalline.Presentation.affineScheme k C) U
  let : Algebra C Γ(Spec (CommRingCat.of C), U) := coordinateAlgebra C U
  exact IsScalarTower.of_algebraMap_eq (fun r => DFunLike.congr_fun (sectionBaseMap k C U) r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.Towers
