import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Divisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PrincipalChow

/-! # Divisor Chow -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: rational-section divisors give the same Chow class after changing the nonzero coefficient -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycle_dimension (x : X) (hx : L.rationalSectionPointCycle x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f :=
  DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x (L.rationalSectionPointCycle_coheight x hx)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionChowClass (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f d := Point.CycleChow.BundleCycles.pointCycleToChowQ f d L.rationalSectionPointCycle

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionChowClass_coefficient_independent (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) (a : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (L.rationalSectionPointCycleWithCoefficient a) = L.rationalSectionChowClass f d := by
  rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionPointCycleWithCoefficient_eq, map_add, Integral.PrincipalChow.BundleCycles.integralPrincipalPointClass_zero X f d hd, zero_add]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
