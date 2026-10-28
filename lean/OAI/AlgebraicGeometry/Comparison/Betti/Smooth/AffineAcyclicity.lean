import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames
import OAI.AlgebraicGeometry.Comparison.Betti.LocalFormAcyclicity

/-! # Affine Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.AffineAcyclicity

noncomputable section

/-! The original form sheaves are acyclic on every smooth affine scheme and affine open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem smooth_algebraicForms_acyclic (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [IsAffine X.left]
    (n q : ℕ) : Subsingleton (Sheaf.H (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n) (q + 1)) := by
  have : (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n).IsQuasicoherent :=
    ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X n
  let H := Sheaf.functorH (Opens.grothendieckTopology X.left) (q + 1)
  have : Subsingleton (H.obj ((SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).obj
      (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n))) :=
    SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) q
  let e := H.mapIso (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X n)
  exact (ConcreteCategory.bijective_of_isIso e.hom).surjective.subsingleton

theorem smooth_affineOpen_algebraicForms_acyclic (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U) (n q : ℕ) :
    Subsingleton (Sheaf.H ((LocalFormAcyclicity.additiveZariskiOpenRestriction (Open.AffineIsoEvaluation.openInclusion X U)).obj
      (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n)) (q + 1)) := by
  have : IsAffine (Open.AffineIsoEvaluation.openOver X U).left := hU
  have : Smooth (Open.AffineIsoEvaluation.openOver X U).hom := inferInstanceAs (Smooth (U.ι ≫ X.hom))
  let H := Sheaf.functorH (Opens.grothendieckTopology (Open.AffineIsoEvaluation.openOver X U).left) (q + 1)
  have : Subsingleton (H.obj (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf (Open.AffineIsoEvaluation.openOver X U) n)) :=
    smooth_algebraicForms_acyclic (Open.AffineIsoEvaluation.openOver X U) n q
  let e := H.mapIso (LocalFormAcyclicity.algebraicFormAdditiveOpenRestrictionIso (Open.AffineIsoEvaluation.openInclusion X U) n)
  exact (ConcreteCategory.bijective_of_isIso e.hom).injective.subsingleton

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.AffineAcyclicity
