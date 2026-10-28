import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantGlobalFrame
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.PrincipalPullbackProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismRestrictGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian

/-! # Proper Global Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperGlobalProjection.Cycles

noncomputable section

section

/-! # LineBundleCycles: exact proper projection of actual rational-section divisors in a global frame -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y} (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule Y)

include gY e in
theorem properPushforward_lineBundleSection_globalFrame (a : Y.functionFieldˣ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
        ((L.pullback f).rationalSectionPointCycleWithCoefficient (L.dominantPullbackSectionCoefficient f hη a)) =
      (f.residueDegree (genericPoint X) : ℚ) • L.rationalSectionPointCycleWithCoefficient a := by
  rw [GlobalDivisor.Cycles.lineBundleGlobal_section_pointCycle (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e f),
    DominantGlobalFrame.Cycles.dominantPullbackSectionCoefficient_globalFrame f hη e a,
    GlobalDivisor.Cycles.lineBundleGlobal_section_pointCycle e a]
  exact Proper.PrincipalPullbackProjection.BundleCycles.properPushforward_pulledPrincipalDivisor f hη gY (a * GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient e)

end

/-! # LineBundleCycles: exact proper projection for actual rational-section divisors of arbitrary algebraic line bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    [X.IsSeparated] [Y.IsSeparated]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

omit [X.IsSeparated] [Y.IsSeparated] in
include gY in
theorem properPushforward_lineBundleSection_onOpen (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    [IsIntegral U.toScheme] [IsIntegral (f ⁻¹ᵁ U).toScheme]
    [AlgebraicGeometry.IsNoetherian U.toScheme] [AlgebraicGeometry.IsNoetherian (f ⁻¹ᵁ U).toScheme]
    [U.toScheme.IsSeparated] [(f ⁻¹ᵁ U).toScheme.IsSeparated]
    (e : (L.pullback U.ι).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme) (a : Y.functionFieldˣ) :
    Finsupp.comapDomain U.ι
        (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f ((L.pullback f).rationalSectionPointCycleWithCoefficient
          (L.dominantPullbackSectionCoefficient f hη a))) U.ι.isOpenEmbedding.injective.injOn =
      (f.residueDegree (genericPoint X) : ℚ) •
        Finsupp.comapDomain U.ι (L.rationalSectionPointCycleWithCoefficient a) U.ι.isOpenEmbedding.injective.injOn := by
  let q := f ∣_ U
  have hq := MorphismRestrictGenericPoint.BundleCycles.morphismRestrict_genericPoint f hη U
  have hsec := DominantOpenCycle.Cycles.dominantPullback_section_openSquare f (f ⁻¹ᵁ U).ι U.ι q
    (morphismRestrict_ι f U).symm hη hq L a
  have hp := Open.FiberPushforward.BundleCycles.morphismRestrict_pointPushforward f U
    ((L.pullback f).rationalSectionPointCycleWithCoefficient (L.dominantPullbackSectionCoefficient f hη a))
  have hl := properPushforward_lineBundleSection_globalFrame q hq (U.ι ≫ gY) e
    (L.openPullbackSectionCoefficient U.ι a)
  have hd := MorphismRestrictGenericPoint.BundleCycles.morphismRestrict_genericResidueDegree f U
  have ht := L.openPullback_section_pointCycle U.ι a
  exact hp.symm.trans ((congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward q) hsec.symm).trans
    (hl.trans (congrArg₂ (fun n : ℚ => fun z : U.toScheme →₀ ℚ => n • z)
      (congrArg (fun n : ℕ => (n : ℚ)) hd) ht)))

include gY in
theorem properPushforward_lineBundleSection (a : Y.functionFieldˣ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f ((L.pullback f).rationalSectionPointCycleWithCoefficient
        (L.dominantPullbackSectionCoefficient f hη a)) =
      (f.residueDegree (genericPoint X) : ℚ) • L.rationalSectionPointCycleWithCoefficient a := by
  ext y
  let U := L.trivializingOpen y
  let : Nonempty U := ⟨⟨y, L.mem_trivializingOpen y⟩⟩
  let : Nonempty (f ⁻¹ᵁ U) := DominantReferencePullback.Cycles.genericPointMap_preimage_nonempty f hη U
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  let : AlgebraicGeometry.IsNoetherian U.toScheme := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian U.ι
  let : AlgebraicGeometry.IsNoetherian (f ⁻¹ᵁ U).toScheme := Open.ImmersionNoetherian.BundleCycles.openImmersion_isNoetherian (f ⁻¹ᵁ U).ι
  let : U.toScheme.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from U.ι]
    infer_instance⟩
  let : (f ⁻¹ᵁ U).toScheme.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (f ⁻¹ᵁ U).ι]
    infer_instance⟩
  let e : (L.pullback U.ι).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme :=
    (L.restrictToOpenPullbackIso U.ι).symm ≪≫ L.trivialization y
  have h := properPushforward_lineBundleSection_onOpen f hη gY L U e a
  exact congrArg (fun c : U.toScheme →₀ ℚ => c ⟨y, L.mem_trivializingOpen y⟩) h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperGlobalProjection.Cycles
