import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorQuasicoherent
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleForget
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing

/-! # Exterior Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorAcyclicity

noncomputable section

/-! Actual algebraic form sheaves on standard smooth affine charts are acyclic in positive degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
  [Algebra.IsStandardSmooth ℂ (ExteriorRestrictions.globalCoordinateAlgebra X)]

def algebraicFormAdditiveSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0} :=
  (sheafCompose (Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj ((Algebraic.Sheaves.algebraicDeRhamSheafComplex X).X n)

theorem standardSmooth_algebraicForms_acyclic (n q : ℕ) :
    Subsingleton (Sheaf.H (algebraicFormAdditiveSheaf X n) (q + 1)) := by
  have : (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsQuasicoherent :=
    ExteriorQuasicoherent.standardSmooth_exteriorFormsModuleSheaf_quasicoherent X n
  let H := Sheaf.functorH (Opens.grothendieckTopology X.left) (q + 1)
  have : Subsingleton (H.obj ((SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).obj
      (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n))) :=
    SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) q
  let e := H.mapIso (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X n)
  exact (ConcreteCategory.bijective_of_isIso e.hom).surjective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorAcyclicity
