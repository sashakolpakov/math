import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.SectionUnit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf

/-! # Global Section Functor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionFunctor.CechGlobalSectionFunctor

noncomputable section

/-! Actual global sections of the native Čech sheaf resolution are naturally the direct Čech cochains of the original sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type u} (U : ι → X.left.Opens)

def presheafIso : SectionUnit.CechSectionUnit.presheafSections R X.left U ≅ NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf.functor R X U := by
  let P := Presheaf.CechPresheaf.Presheaves R X.left
  let E := (FormalCoproduct.mk ι U).cech
  let G : P ⥤ ModuleCat.{u} R := GlobalCoefficients.CechGlobalCoefficients.evaluate R X
  let C₁ : (X.left.Opensᵒᵖ ⥤ P) ⥤ CochainComplex P ℕ := FormalCoproduct.cochainComplexFunctor E
  let C₂ : P ⥤ CochainComplex (ModuleCat.{u} R) ℕ := FormalCoproduct.cochainComplexFunctor E
  let W : (X.left.Opensᵒᵖ ⥤ P) ⥤ P := (Functor.whiskeringRight X.left.Opensᵒᵖ P (ModuleCat.{u} R)).obj G
  let F : P ⥤ (X.left.Opensᵒᵖ ⥤ P) := MixedCech.Functor.MixedCechFunctor.coefficients R X.left
  let T := G.mapHomologicalComplex (.up ℕ)
  let hc : C₁ ⋙ T ≅ W ⋙ C₂ := CoefficientChangeNaturality.CechCoefficientChangeNaturality.iso G E
  let hi : F ⋙ W ≅ 𝟭 P := GlobalCoefficients.CechGlobalCoefficients.iso R X
  let inner : (F ⋙ C₁) ⋙ T ≅ C₂ :=
    Functor.associator F C₁ T ≪≫ Functor.isoWhiskerLeft F hc ≪≫
      (Functor.associator F W C₂).symm ≪≫ Functor.isoWhiskerRight hi C₂ ≪≫ Functor.leftUnitor C₂
  exact Functor.isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} R)) inner

def iso : SectionUnit.CechSectionUnit.sheafSections R X.left U ≅ NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf.functor R X U :=
  (SectionUnit.CechSectionUnit.iso R X.left U).symm ≪≫ presheafIso R X U

instance sheafSections_additive : (SectionUnit.CechSectionUnit.sheafSections R X.left U).Additive :=
  Functor.additive_of_iso (iso R X U).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.GlobalSectionFunctor.CechGlobalSectionFunctor
