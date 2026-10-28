import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OrdinaryCech
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechIdentification

/-! # Concrete Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConcreteCech

noncomputable section

/-! The actual algebraic-to-smooth sheaf map induces the ordinary Čech comparison with its section normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def algebraicSheafPresheafComplex : CochainComplex (Sheaf.CochainPullback.ComplexPresheaves X) ℕ :=
  Complex.SheafCechBicomplex.complexSheafPresheafComplex (TopCat.of X.left) (Algebraic.Sheaves.algebraicDeRhamSheafComplex X)

def algebraicSheafToSmoothPresheafMap :
    algebraicSheafPresheafComplex X ⟶ Betti.Smooth.SheafMap.zariskiSmoothPresheafComplex X :=
  ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
    (.up ℕ)).map (Betti.Smooth.SheafMap.algebraicToSmoothSheafMap X)

def algebraicPresheafSheafificationUnit :
    Algebraic.Sheaves.deRhamPresheafComplex X ⟶ algebraicSheafPresheafComplex X :=
  (Sheaf.CochainPullback.sheafificationComplexAdjunction X).unit.app (Algebraic.Sheaves.deRhamPresheafComplex X)

theorem algebraicSheafToSmoothPresheafMap_normalization :
    algebraicPresheafSheafificationUnit X ≫ algebraicSheafToSmoothPresheafMap X =
      Betti.Smooth.SheafMap.presheafSmoothCochainMap X :=
  Betti.Smooth.SheafMap.algebraicToSmoothSheafMap_normalization X

variable {ι : Type} (U : ι → X.left.Opens)

def algebraicToSmoothCechMap :
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalComplex U (algebraicSheafPresheafComplex X) ⟶
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RegularSmoothness.NativeModel X) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i)) :=
  AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalMap U (algebraicSheafToSmoothPresheafMap X) ≫
    (Analytic.CechIdentification.zariskiSmoothCechTotalIso X U).hom

def algebraicToSmoothCechMapInt :
    Algebraic.OrdinaryCech.algebraicOrdinaryCechTotalInt X U ⟶
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RegularSmoothness.NativeModel X) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).extend
        (ComplexShape.embeddingUpIntGE 0) :=
  HomologicalComplex.extendMap (algebraicToSmoothCechMap X U) (ComplexShape.embeddingUpIntGE 0)

theorem algebraicToSmoothCechMap_normalization :
    AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalMap U (algebraicPresheafSheafificationUnit X) ≫
        algebraicToSmoothCechMap X U =
      AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalMap U (Betti.Smooth.SheafMap.presheafSmoothCochainMap X) ≫
        (Analytic.CechIdentification.zariskiSmoothCechTotalIso X U).hom := by
  change (AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalFunctor U).map _ ≫
      ((AlgebraicTopology.DeRham.Comparison.CechTotalFunctor.cechTotalFunctor U).map _ ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, algebraicSheafToSmoothPresheafMap_normalization]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConcreteCech
