import OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealEquation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularOrder
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow

/-! # Ideal Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisor.BundleCycles

noncomputable section

/-! The actual invertible ideal represents minus its effective
Cartier divisor, with the local equation quotient lengths as multiplicities. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X Z : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (i : Z ⟶ X) [QuasiCompact i] (hi : IdealBundle.Cycles.HasRegularPrincipalImageIdeals i)

def cartierIdealInverseCoefficient : X.functionFieldˣ :=
  LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismInverseCoefficient (IdealBundle.Cycles.cartierIdealLineBundle i hi) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i)
    (IdealEquation.BundleCycles.cartierIdealMorphismFieldCoordinate_ne_zero i hi (genericPoint X))

theorem cartierIdealInverseCoefficient_divisor (x : X) :
    (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (cartierIdealInverseCoefficient i hi) x =
        -X.ord (X.germToFunctionField ((IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x)
          (IdealEquation.BundleCycles.cartierIdealEquation i hi x)) x :=
  LineBundle.MorphismRationalCoordinate.Cycles.lineBundleMorphismInverseCoefficient_divisor (IdealBundle.Cycles.cartierIdealLineBundle i hi) (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion i)
    (IdealEquation.BundleCycles.cartierIdealMorphismFieldCoordinate_ne_zero i hi (genericPoint X)) x

theorem cartierIdealInverseCoefficient_divisor_length (x : X) (hx : coheight x = 1) :
    (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (cartierIdealInverseCoefficient i hi) x =
        -((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸ Ideal.span {X.presheaf.germ
            ((IdealBundle.Cycles.cartierIdealLineBundle i hi).trivializingOpen x) x
              ((IdealBundle.Cycles.cartierIdealLineBundle i hi).mem_trivializingOpen x) (IdealEquation.BundleCycles.cartierIdealEquation i hi x)})).toNat : ℤ) := by
  rw [cartierIdealInverseCoefficient_divisor]
  exact congrArg Neg.neg (Open.RegularOrder.BundleCycles.openRegular_order_length _ _ (IdealEquation.BundleCycles.cartierIdealEquation_ne_zero i hi x) x
    ((IdealBundle.Cycles.cartierIdealLineBundle i hi).mem_trivializingOpen x) hx)

theorem cartierIdealInverseCoefficient_divisor_nonpositive (x : X) :
    (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointDivisorWithCoefficient
      (cartierIdealInverseCoefficient i hi) x ≤ 0 := by
  rw [cartierIdealInverseCoefficient_divisor]
  exact neg_nonpos.mpr (Open.RegularOrder.BundleCycles.openRegular_order_nonnegative _ _ (IdealEquation.BundleCycles.cartierIdealEquation_ne_zero i hi x) x
    ((IdealBundle.Cycles.cartierIdealLineBundle i hi).mem_trivializingOpen x))

def cartierIdealInversePointCycle : X →₀ ℚ :=
  (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionPointCycleWithCoefficient (cartierIdealInverseCoefficient i hi)

theorem cartierIdealInversePointCycle_class (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (cartierIdealInversePointCycle i hi) =
      (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionChowClass f d :=
  (IdealBundle.Cycles.cartierIdealLineBundle i hi).rationalSectionChowClass_coefficient_independent f d hd
    (cartierIdealInverseCoefficient i hi)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.IdealDivisor.BundleCycles
