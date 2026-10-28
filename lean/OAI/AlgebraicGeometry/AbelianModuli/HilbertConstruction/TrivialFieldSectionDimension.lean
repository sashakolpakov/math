import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.StructureModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalFunctionDimension

/-! # Trivial Field Section Dimension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialFieldSectionDimension

noncomputable section

/-! A trivial module on a field scheme whose global functions are the ground field has one-dimensional actual coefficient sections. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem trivialModule_coefficientSections_finrank_one
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) [IsIso p.appTop]
    (M : X.Modules) (e : M ≅ Line.Bundles.structureModule X) :
    Module.finrank K ((Coefficient.ModulePresheaf.coefficientModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) M).obj (op ⊤)) = 1 := by
  let c := Affine.ChartCoefficientSections.schemeGlobalCoefficient p
  let eM := ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).mapIso e).app (op ⊤)
  let eO : (Coefficient.ModulePresheaf.coefficientModulePresheaf c (Line.Bundles.structureModule X)).obj (op ⊤) ≃ₗ[K]
      Coefficient.AlgebraPresheaf.coefficientAlgebraSections c ⊤ := Coefficient.StructureModuleComparison.coefficientStructureModuleComponent c ⊤
  exact (eM.toLinearEquiv.trans eO).finrank_eq.trans
    ((Coefficient.GlobalFunctionDimension.coefficientGlobalFunctionDimension_eq_one_iff_iso p).mpr inferInstance)

theorem properSmoothConnected_trivialModule_coefficientSections_finrank_one
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [IsProper p] [Smooth p] [GeometricallyConnected p]
    (x : Spec (.of K) ⟶ X) (hx : x ≫ p = 𝟙 _)
    (M : X.Modules) (e : M ≅ Line.Bundles.structureModule X) :
    Module.finrank K ((Coefficient.ModulePresheaf.coefficientModulePresheaf (Affine.ChartCoefficientSections.schemeGlobalCoefficient p) M).obj (op ⊤)) = 1 := by
  have : IsIso p.appTop :=
    (HilbertConstruction.Field.GlobalFunctionsConnectedness.properSmoothPointed_geometricallyConnected_iff_globalFunctionsIso p x hx).mp inferInstance
  exact trivialModule_coefficientSections_finrank_one p M e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TrivialFieldSectionDimension
