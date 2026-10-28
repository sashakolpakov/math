import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCoordinateIdentity
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DivisorChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ChowPointClass

/-! # Open Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles

noncomputable section

section

/-! # LineBundleCycles: genuine open restriction of rational-section divisors and their Chow classes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (i : Y ⟶ X) [IsOpenImmersion i]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_order [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : Y) :
    (L.restrictToOpen i).rationalSectionOrder x =
      L.rationalSectionOrder (i x) + Y.ord (L.openRationalCoefficient i).val x := by
  have h := congrArg (fun a : Y.functionFieldˣ => Y.ord a.val x) (L.open_coordinate_identity i x)
  change Y.ord ((FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm (L.openLocalDomain i x) (L.openLocalUnit i x)).val *
    ((L.restrictToOpen i).rationalSectionCoordinate x).val) x =
    Y.ord ((Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i (L.rationalSectionCoordinate (i x))).val *
      (L.openRationalCoefficient i).val) x at h
  rw [Scheme.ord_mul (FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm _ _).ne_zero
      ((L.restrictToOpen i).rationalSectionCoordinate_ne_zero x),
    FunctionFieldUnitGerm.BundleCycles.functionFieldUnitGerm_order _ _ x (L.mem_openLocalDomain i x), zero_add,
    Scheme.ord_mul (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i _).ne_zero (L.openRationalCoefficient i).ne_zero,
    Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_order] at h
  exact h

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_divisor :
    (L.restrictToOpen i).rationalSectionPointDivisor =
      Finsupp.comapDomain i L.rationalSectionPointDivisor i.isOpenEmbedding.injective.injOn +
        Ord.BundleCycles.principalDivisor Y (L.openRationalCoefficient i).val := by
  ext x
  exact L.open_order i x

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_pointCycle :
    (L.restrictToOpen i).rationalSectionPointCycle =
      Finsupp.comapDomain i L.rationalSectionPointCycle i.isOpenEmbedding.injective.injOn +
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (L.openRationalCoefficient i).val := by
  ext x
  exact (congrArg (fun n : ℤ => (n : ℚ)) (L.open_order i x)).trans (Int.cast_add _ _)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_chowClass (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    (L.restrictToOpen i).rationalSectionChowClass (i ≫ f) d =
      Open.ChowRestriction.BundleCycles.openChowRestriction i f d (L.rationalSectionChowClass f d) := by
  have hdY : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) = d + 1 :=
    (Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i f).trans hd
  change Point.CycleChow.BundleCycles.pointCycleToChowQ (i ≫ f) d (L.restrictToOpen i).rationalSectionPointCycle =
    Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d L.rationalSectionPointCycle)
  rw [L.open_pointCycle i, map_add, Integral.PrincipalChow.BundleCycles.integralPrincipalPointClass_zero Y (i ≫ f) d hdY,
    add_zero, Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.pullback_open_chowClass (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    (L.pullback i).rationalSectionChowClass (i ≫ f) d =
      Open.ChowRestriction.BundleCycles.openChowRestriction i f d (L.rationalSectionChowClass f d) := by
  rw [← LineBundle.IsoDivisor.Cycles.lineBundleIso_chowClass (L.restrictToOpenPullbackIso i) (i ≫ f) d
    ((Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i f).trans hd)]
  exact L.open_chowClass i f d hd

end

/-! # LineBundleCycles: transport of the same actual rational section through sheaf isomorphisms and open restriction -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}

def LineBundle.OpenDivisor.Cycles.lineBundleIsoSectionCoefficient (e : L.sheaf ≅ M.sheaf) (a : X.functionFieldˣ) : X.functionFieldˣ :=
  a * LineBundle.IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e

theorem LineBundle.OpenDivisor.Cycles.lineBundleIso_section_divisor (e : L.sheaf ≅ M.sheaf) (a : X.functionFieldˣ) :
    M.rationalSectionPointDivisorWithCoefficient (LineBundle.OpenDivisor.Cycles.lineBundleIsoSectionCoefficient e a) =
      L.rationalSectionPointDivisorWithCoefficient a := by
  change Ord.BundleCycles.principalDivisor X (a.val * (LineBundle.IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).val) + M.rationalSectionPointDivisor = _
  rw [Ord.BundleCycles.principalDivisor_mul X _ _ a.ne_zero (LineBundle.IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient e).ne_zero]
  change _ = Ord.BundleCycles.principalDivisor X a.val + L.rationalSectionPointDivisor
  rw [LineBundle.IsoDivisor.Cycles.lineBundleIso_divisor e]
  abel

variable {Y : Scheme.{0}} [IsIntegral Y] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i]

def Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionCoefficient (a : X.functionFieldˣ) : Y.functionFieldˣ :=
  Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i a / L.openRationalCoefficient i

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionCoefficient_order (a : X.functionFieldˣ) (y : Y) :
    Y.ord (L.openSectionCoefficient i a).val y + Y.ord (L.openRationalCoefficient i).val y =
      X.ord a.val (i y) := by
  have h := congrArg (fun u : Y.functionFieldˣ => Y.ord u.val y)
    (div_mul_cancel (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i a) (L.openRationalCoefficient i))
  change Y.ord ((L.openSectionCoefficient i a).val * (L.openRationalCoefficient i).val) y =
    Y.ord (Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits i a).val y at h
  rw [Scheme.ord_mul (L.openSectionCoefficient i a).ne_zero (L.openRationalCoefficient i).ne_zero,
    Open.FunctionFieldUnits.BundleCycles.openFunctionFieldUnits_order] at h
  exact h

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.open_section_divisor (a : X.functionFieldˣ) :
    (L.restrictToOpen i).rationalSectionPointDivisorWithCoefficient (L.openSectionCoefficient i a) =
      Finsupp.comapDomain i (L.rationalSectionPointDivisorWithCoefficient a) i.isOpenEmbedding.injective.injOn := by
  ext y
  change Y.ord (L.openSectionCoefficient i a).val y + (L.restrictToOpen i).rationalSectionOrder y =
    X.ord a.val (i y) + L.rationalSectionOrder (i y)
  rw [L.open_order i y]
  have h := L.openSectionCoefficient_order i a y
  omega

end

end OAI.AlgebraicGeometry.Divisors.LineBundles
