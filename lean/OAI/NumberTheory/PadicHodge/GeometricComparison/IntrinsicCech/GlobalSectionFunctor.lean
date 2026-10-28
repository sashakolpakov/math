import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.SectionUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalCoefficients
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf

/-! # Global Section Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor

noncomputable section

/-! Actual global sections of the native Čech sheaf resolution are naturally the direct Čech cochains of the original sheaf. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens)

def presheafIso : SectionUnit.IntrinsicCechSectionUnit.presheafSections R X.left U ≅ Cech.CechSheaf.functor R X U := by
  let P := AlgebraicGeometry.Crystalline.Cohomology.Cech.Presheaf.CechPresheaf.Presheaves R X.left
  let E := (FormalCoproduct.mk ι U).cech
  let G : P ⥤ ModuleCat.{0} R := GlobalCoefficients.IntrinsicCechGlobalCoefficients.evaluate R X
  let C₁ : (X.left.Opensᵒᵖ ⥤ P) ⥤ CochainComplex P ℕ := FormalCoproduct.cochainComplexFunctor E
  let C₂ : P ⥤ CochainComplex (ModuleCat.{0} R) ℕ := FormalCoproduct.cochainComplexFunctor E
  let W : (X.left.Opensᵒᵖ ⥤ P) ⥤ P := (Functor.whiskeringRight X.left.Opensᵒᵖ P (ModuleCat.{0} R)).obj G
  let F : P ⥤ (X.left.Opensᵒᵖ ⥤ P) := IntrinsicCech.Functor.IntrinsicCechFunctor.coefficients R X.left
  let T := G.mapHomologicalComplex (.up ℕ)
  let hc : C₁ ⋙ T ≅ W ⋙ C₂ := AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.iso G E
  let hi : F ⋙ W ≅ 𝟭 P := GlobalCoefficients.IntrinsicCechGlobalCoefficients.iso R X
  let inner : (F ⋙ C₁) ⋙ T ≅ C₂ :=
    Functor.associator F C₁ T ≪≫ Functor.isoWhiskerLeft F hc ≪≫
      (Functor.associator F W C₂).symm ≪≫ Functor.isoWhiskerRight hi C₂ ≪≫ Functor.leftUnitor C₂
  exact Functor.isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} R)) inner

def iso : SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U ≅ Cech.CechSheaf.functor R X U :=
  (SectionUnit.IntrinsicCechSectionUnit.iso R X.left U).symm ≪≫ presheafIso R X U

instance sheafSections_additive : (SectionUnit.IntrinsicCechSectionUnit.sheafSections R X.left U).Additive :=
  Functor.additive_of_iso (iso R X U).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.GlobalSectionFunctor.IntrinsicCechGlobalSectionFunctor
