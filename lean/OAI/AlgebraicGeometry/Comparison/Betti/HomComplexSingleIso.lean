import OAI.AlgebraicGeometry.Comparison.Betti.IntegerAcyclicHomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # Hom Complex Single Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomComplexSingleIso.Ext

noncomputable section

/-! The ordinary Hom complex identifies with the Hom complex from a single object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.CochainComplex _root_.CochainComplex.HomComplex

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
  (A : C) (K : CochainComplex C ℤ)

def integerHomSingleComponentIso (n : ℤ) :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).X n ≅
      (HomComplex ((CochainComplex.singleFunctor C 0).obj A) K).X n :=
  (Cochain.fromSingleEquiv (X := A) (K := K) (zero_add n)).symm.toAddCommGrpIso

theorem integerHomSingleComponentIso_comm (i j : ℤ) :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).d i j ≫ (integerHomSingleComponentIso A K j).hom =
      (integerHomSingleComponentIso A K i).hom ≫
        (HomComplex ((CochainComplex.singleFunctor C 0).obj A) K).d i j := by
  ext f
  exact (Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)).symm

def integerHomSingleIso : IntegerAcyclicHomComplex.Ext.integerHomComplex A K ≅
    HomComplex ((CochainComplex.singleFunctor C 0).obj A) K :=
  HomologicalComplex.Hom.isoOfComponents (integerHomSingleComponentIso A K)
    (fun i j _ => (integerHomSingleComponentIso_comm A K i j).symm)

def integerHomCohomologyClassEquiv (n : ℤ) :
    (IntegerAcyclicHomComplex.Ext.integerHomComplex A K).homology n ≃+
      CohomologyClass ((CochainComplex.singleFunctor C 0).obj A) K n :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) n).mapIso
    (integerHomSingleIso A K)).addCommGroupIsoToAddEquiv.trans
      (homologyAddEquiv _ K n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomComplexSingleIso.Ext
