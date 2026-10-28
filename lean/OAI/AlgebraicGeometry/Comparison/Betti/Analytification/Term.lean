import OAI.AlgebraicGeometry.Comparison.Betti.Module.Normalization
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.HolomorphicModuleIso

/-! # Term -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Term

noncomputable section

/-! In every degree the original comparison is the actual ringed
analytification unit followed by the proved holomorphic form identification.
This normalization isolates the genuine proper cohomology comparison that
is still required; no cohomological isomorphism is assumed here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analytifiedExteriorHolomorphicIso (n : ℕ) :
    (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n) ≅
      AnalytifiedForm.analyticHolomorphicFormModuleSheaf X n := by
  have := Betti.Smooth.HolomorphicModuleIso.analytifiedExteriorToHolomorphicModuleMap_isIso X n
  exact asIso (AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n)

def analyticExteriorFormForgetIso (n : ℕ) :
    (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).obj
        ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)) ≅
      (sheafCompose (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          ((Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X).X n) :=
  (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)).mapIso
      (analytifiedExteriorHolomorphicIso X n) ≪≫
    Holomorphic.ModuleForget.holomorphicModuleSheafForgetIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n

/-- The actual comparison is the actual module analytification unit, with
the original algebraic and holomorphic form sheaves identified exactly. -/
theorem algebraicToHolomorphicSheafMap_eq_analytificationUnit (n : ℕ) :
    (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X n).hom ≫
      (sheafCompose (Opens.grothendieckTopology X.left)
        (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).map
          ((Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X).f n) =
    (SheafOfModules.toSheaf.{0} X.left.ringCatSheaf).map
        ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X n)) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat (Base.analytificationMap X)).map
        (analyticExteriorFormForgetIso X n).hom := by
  rw [Module.Normalization.exteriorToHolomorphicModuleSheafMap_forget]
  have h := ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).homEquiv_unit _ _
    (AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap X n)).symm.trans
      (AnalytifiedForm.analytifiedExteriorToHolomorphicModuleMap_adjunction X n)
  rw [← h]
  erw [Functor.map_comp, Category.assoc]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Term
