import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses
import OAI.AlgebraicGeometry.DivisorClass.Chern.Singular.CechDescent
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.BettiSheafComparison
import OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison

/-! # Cech Sheafification -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Singular

noncomputable section

/-! Sheafification preserves the actual cochains and both equations of singular Cech descent. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Cohomology.Singular.OpenSheafComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem CechSheafification.abelianCechDelta_forget (F : X.Presheaf (ModuleCat.{0} ℚ)) (n : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain F U n) :
    Abelian.CechCoordinates.abelianCechDelta (F ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget) U n k = Rational.Cech.RationalCech.cechDelta F U n k := by
  funext a
  rw [Rational.Cech.RationalCech.cechDelta_apply]
  rfl

def CechSheafification.rationalSingularSheafUnit (q : ℕ) :
    (AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q ⋙ AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget ⟶
      ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj :=
  Functor.whiskerRight (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
    ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q)) AlgebraicTopology.DeRham.Comparison.RationalSheafForget.rationalForget

def CechSheafification.singularCechSheafify (q p : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    Abelian.CechCoordinates.AbelianCechCochain ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj U p :=
  Abelian.CechClasses.abelianCechCoefficient U (CechSheafification.rationalSingularSheafUnit q) p k

theorem CechSheafification.singularCechSheafify_delta (q p : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    CechSheafification.singularCechSheafify U q (p + 1)
        (Rational.Cech.RationalCech.cechDelta ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p k) =
      Abelian.CechCoordinates.abelianCechDelta ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X q).obj U p
        (CechSheafification.singularCechSheafify U q p k) := by
  rw [← CechSheafification.abelianCechDelta_forget]
  exact Abelian.CechClasses.abelianCechCoefficient_delta U (CechSheafification.rationalSingularSheafUnit q) p k

theorem CechSheafification.singularCechSheafify_d (q p : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).X q) U p) :
    Abelian.CechClasses.abelianCechCoefficient U ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d q (q + 1)).hom p
        (CechSheafification.singularCechSheafify U q p k) =
      CechSheafification.singularCechSheafify U (q + 1) p
        (Rational.Cech.RationalCech.cechCoefficientMap U ((AlgebraicTopology.DeRham.Comparison.SingularPresheaf.singularPresheafComplex (ModuleCat.of ℚ ℚ) X).d q (q + 1)) p k) := by
  funext a
  exact ConcreteCategory.congr_hom
    ((AlgebraicTopology.Cohomology.Singular.OpenSheafComparison.singularCochainsToOpenSheafSections (ModuleCat.of ℚ ℚ) X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)).comm q (q + 1))
    (k a)

theorem CechSheafification.singularCechSheafify_zero (q p : ℕ) : CechSheafification.singularCechSheafify U q p 0 = 0 := by
  funext a
  exact map_zero ((CechSheafification.rationalSingularSheafUnit (X := X) q).app (op (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a))).hom

variable {U} {c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X 2} (d : CechDescent.SingularCechDescentData c U)

theorem CechDescent.SingularCechDescentData.sheafified_horizontal_d :
    Abelian.CechClasses.abelianCechCoefficient U ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 0 1).hom 1
        (CechSheafification.singularCechSheafify U 0 1 d.horizontal) =
      Abelian.CechCoordinates.abelianCechDelta ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).X 1).obj U 0
        (CechSheafification.singularCechSheafify U 1 0 d.vertical) := by
  rw [CechSheafification.singularCechSheafify_d, d.horizontal_d, CechSheafification.singularCechSheafify_delta]

theorem CechDescent.SingularCechDescentData.sheafified_vertical_d :
    Abelian.CechClasses.abelianCechCoefficient U ((Rational.BettiSheafComparison.rationalAbelianSingularResolution X).d 1 2).hom 0
        (CechSheafification.singularCechSheafify U 1 0 d.vertical) =
      CechSheafification.singularCechSheafify U 2 0
        ((Rational.CechComparison.RationalCech.globalSingularCechColumnAugmentation X U (ModuleCat.of ℚ ℚ)).f 2 c.val) := by
  rw [CechSheafification.singularCechSheafify_d, d.vertical_d]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Singular
