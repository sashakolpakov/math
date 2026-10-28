import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.CechClasses
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechRepresentative
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod

/-! # Integral Cech Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechSheaf

noncomputable section

/-! Integral Cech cocycles give actual integral sheaf classes, naturally under rationalization. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} {I : Type} (U : I → Opens X)

theorem rationalCechAbelianDelta (n : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n) :
    Abelian.CechCoordinates.abelianCechDelta (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X).obj U n k =
      Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n k := by
  funext a
  rw [Rational.Cech.RationalCech.cechDelta_apply]
  rfl

def integerCechSheafClass (hU : ⨆ i, U i = ⊤) (n : ℕ)
    (g : Cech.IntegralRefinement.IntegerCechCochain U (n + 1)) (hg : Cech.IntegralRefinement.integerCechDelta U (n + 1) g = 0) :
    CategoryTheory.Sheaf.H (IntegralConstantSheaf.integralConstantSheaf X) (n + 1) :=
  Abelian.CechClasses.abelianCechSheafClass U (IntegralConstantSheaf.integralConstantSheaf X) hU n g hg

def rationalCechSheafClass (hU : ⨆ i, U i = ⊤) (n : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U (n + 1))
    (hk : Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U (n + 1) k = 0) :
    CategoryTheory.Sheaf.H (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) (n + 1) :=
  Abelian.CechClasses.abelianCechSheafClass U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) hU n k
    ((rationalCechAbelianDelta U (n + 1) k).trans hk)

theorem rationalCech_nsmul_closed (n N : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n)
    (hk : Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n k = 0) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n (N • k) = 0 := by
  rw [map_nsmul, hk, smul_zero]

theorem rationalCechSheafClass_nsmul (hU : ⨆ i, U i = ⊤) (n N : ℕ)
    (k : Rational.Cech.RationalCech.CechCochain (Cech.Obj.RationalCech.locallyConstantPresheaf X) U (n + 1))
    (hk : Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U (n + 1) k = 0) :
    rationalCechSheafClass U hU n (N • k) (rationalCech_nsmul_closed U (n + 1) N k hk) =
      N • rationalCechSheafClass U hU n k hk :=
  Abelian.CechClasses.abelianCechSheafClass_nsmul U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf X) hU n N k
    ((rationalCechAbelianDelta U (n + 1) k).trans hk)

theorem integerCechRationalize_closed (n : ℕ) (g : Cech.IntegralRefinement.IntegerCechCochain U n)
    (hg : Cech.IntegralRefinement.integerCechDelta U n g = 0) :
    Rational.Cech.RationalCech.cechDelta (Cech.Obj.RationalCech.locallyConstantPresheaf X) U n (Cech.IntegralRefinement.integerCechRationalize U n g) = 0 := by
  erw [← Cech.IntegralRefinement.integerCechRationalize_delta, hg, map_zero]

theorem integerCechSheafClass_rationalize (hU : ⨆ i, U i = ⊤) (n : ℕ)
    (g : Cech.IntegralRefinement.IntegerCechCochain U (n + 1)) (hg : Cech.IntegralRefinement.integerCechDelta U (n + 1) g = 0) :
    CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) (n + 1)
        (integerCechSheafClass U hU n g hg) =
      rationalCechSheafClass U hU n (Cech.IntegralRefinement.integerCechRationalize U (n + 1) g)
        (integerCechRationalize_closed U (n + 1) g hg) := by
  exact Abelian.CechClasses.abelianCechSheafClass_naturality U (Rational.HolomorphicPeriod.integralToRationalConstantSheaf X) hU n g hg

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralCechSheaf
