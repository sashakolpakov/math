import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RationalSectionRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection

/-! # Canonical Rational Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

/-! # LineBundleCycles: the canonical restricted rational section represents line-bundle intersection on a prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (a : X.functionFieldˣ) (x : X) (hx : coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a x = 0)

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionRestrictionCoefficient :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionFieldˣ :=
  (Classical.choice (L.rationalSectionUnitNeighborhood_nonempty a x hx ha)).restrictionCoefficient

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionRestrictionCoefficient_eq (D : L.RationalSectionUnitNeighborhood a x) :
    L.rationalSectionRestrictionCoefficient a x hx ha = D.restrictionCoefficient :=
  LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.RationalSectionUnitNeighborhood.restrictionCoefficient_independent _ D

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.restrictedRationalSectionPointCycle : X →₀ ℚ :=
  LineBundle.Intersection.Cycles.lineBundleDivisorOnSupportWithCoefficient L (irreducibleSetEquivPoints.symm x)
    (L.rationalSectionRestrictionCoefficient a x hx ha)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.restrictedRationalSectionPointCycle_class (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (L.restrictedRationalSectionPointCycle a x hx ha) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (LineBundle.Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x)) :=
  LineBundle.Intersection.Cycles.lineBundleDivisorOnSupport_class_independent L f d (irreducibleSetEquivPoints.symm x) hd
    (L.rationalSectionRestrictionCoefficient a x hx ha)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.restrictedRationalSectionPointCycle_difference :
    L.restrictedRationalSectionPointCycle a x hx ha =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor (irreducibleSetEquivPoints.symm x)
        (L.rationalSectionRestrictionCoefficient a x hx ha).val +
          LineBundle.Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm x) :=
  LineBundle.Intersection.Cycles.lineBundleDivisorOnSupportWithCoefficient_eq L (irreducibleSetEquivPoints.symm x)
    (L.rationalSectionRestrictionCoefficient a x hx ha)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
