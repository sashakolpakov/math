import OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechBicomplex
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalExtension
import OAI.AlgebraicTopology.DeRham.Comparison.CechTotalFunctor
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # Sheaf Cech Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechTotal

noncomputable section

/-! The sheaf-resolution total is the ordinary Čech total, with the required interchange sign. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable (X : TopCat.{0}) {ι : Type} (U : ι → Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)) ℕ)

def complexSheafCechSectionsTotalInt : CochainComplex AddCommGrpCat.{0} ℤ :=
  ((TotalComplexFunctor.mapBicomplex Cech.FactorSections.sheafTopSections
    (Betti.Sheaf.CechAugmentation.sheafCechBicomplex U
      (((ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive X).mapHomologicalComplex (.up ℕ)).obj K))).total
        (.up ℕ)).extend (ComplexShape.embeddingUpIntGE 0)

def complexSheafOrdinaryCechTotalInt : CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex U (SheafCechBicomplex.complexSheafPresheafComplex X K)).extend
    (ComplexShape.embeddingUpIntGE 0)

def complexSheafCechTotalIso :
    complexSheafCechSectionsTotalInt X U K ≅
      ((forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).obj
        (complexSheafOrdinaryCechTotalInt X U K) := by
  let R := SheafCechBicomplex.complexSheafOrdinaryCechBicomplex X U K
  let F := forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0}
  let E := ComplexShape.embeddingUpIntGE 0
  let e := SheafCechBicomplex.complexSheafCechSectionsBicomplexIso X U K
  exact (E.extendFunctor AddCommGrpCat.{0}).mapIso
      (HomologicalComplex₂.total.mapIso e (.up ℕ)) ≪≫
    Finite.TotalExtension.finiteTotalExtensionIso F R ≪≫
    (F.mapHomologicalComplex (.up ℤ)).mapIso
      ((E.extendFunctor (ModuleCat.{0} ℂ)).mapIso (R.totalFlipIso (.up ℕ)).symm)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Complex.SheafCechTotal
