import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowTransport

/-! # Open Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCycle.Cycles

noncomputable section

/-! # LineBundleCycles: whole rational-section cycles after actual open pullback and sheaf isomorphism -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

theorem lineBundleOpen_pointCycle (i : X ⟶ Y) [IsOpenImmersion i]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (eL : M.sheaf ≅ (L.pullback i).sheaf)
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (g : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType g]
    (h : i ≫ f = g) (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ g d M.rationalSectionPointCycle =
      Point.CycleChow.BundleCycles.pointCycleToChowQ g d
        (Finsupp.comapDomain i L.rationalSectionPointCycle i.isOpenEmbedding.injective.injOn) := by
  have hdX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = d + 1 :=
    (congrArg Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension h.symm).trans
      ((Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i f).trans hd)
  have H := congrArg (DimensionChow.BundleCycles.dimensionChowTransport h d) (L.pullback_open_chowClass i f d hd)
  rw [LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.rationalSectionChowClass_transport] at H
  change (L.pullback i).rationalSectionChowClass g d = DimensionChow.BundleCycles.dimensionChowTransport h d
    (Open.ChowRestriction.BundleCycles.openChowRestriction i f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f d L.rationalSectionPointCycle)) at H
  rw [Open.ChowPointClass.BundleCycles.openChowRestriction_pointClass, Point.ChowTransport.BundleCycles.dimensionChowTransport_pointCycle] at H
  change M.rationalSectionChowClass g d = _
  rw [IsoDivisor.Cycles.lineBundleIso_chowClass eL g d hdX]
  exact H

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenCycle.Cycles
