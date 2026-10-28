import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteGlobalProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.DominantOpenCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismRestrictGenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.ChowPointClass

/-! # Finite Chow Projection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteChowProjection.Cycles

noncomputable section

section

/-! # LineBundleCycles: exact finite projection for actual rational-section divisors of arbitrary algebraic line bundles -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)

include gY in
theorem finitePushforward_lineBundleSection_onOpen (U : Y.Opens) [Nonempty U] [Nonempty (f ⁻¹ᵁ U)]
    [IsIntegral U.toScheme] [IsIntegral (f ⁻¹ᵁ U).toScheme]
    [AlgebraicGeometry.IsNoetherian U.toScheme] [AlgebraicGeometry.IsNoetherian (f ⁻¹ᵁ U).toScheme]
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
  have hl := FiniteGlobalProjection.Cycles.finitePushforward_lineBundleSection_globalFrame q hq (U.ι ≫ gY) e
    (L.openPullbackSectionCoefficient U.ι a)
  have hd := MorphismRestrictGenericPoint.BundleCycles.morphismRestrict_genericResidueDegree f U
  have ht := L.openPullback_section_pointCycle U.ι a
  exact hp.symm.trans ((congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward q) hsec.symm).trans
    (hl.trans (congrArg₂ (fun n : ℚ => fun z : U.toScheme →₀ ℚ => n • z)
      (congrArg (fun n : ℕ => (n : ℚ)) hd) ht)))

include gY in
theorem finitePushforward_lineBundleSection (a : Y.functionFieldˣ) :
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
  let e : (L.pullback U.ι).sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.toScheme :=
    (L.restrictToOpenPullbackIso U.ι).symm ≪≫ L.trivialization y
  have h := finitePushforward_lineBundleSection_onOpen f hη gY L U e a
  exact congrArg (fun c : U.toScheme →₀ ℚ => c ⟨y, L.mem_trivializingOpen y⟩) h

end

/-! # LineBundleCycles: finite projection of actual line-bundle divisor classes with the genuine generic degree -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y)
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY = d + 1)

include hd hη in
theorem finiteChowPushforward_lineBundleClass :
    Finite.ChowPushforward.BundleCycles.finiteChowPushforward f gY d ((L.pullback f).rationalSectionChowClass (f ≫ gY) d) =
      (f.residueDegree (genericPoint X) : ℚ) • L.rationalSectionChowClass gY d := by
  have hdX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY) = d + 1 :=
    (Finite.PointSupport.BundleCycles.schemeDimension_eq_of_finite f hη gY).symm.trans hd
  let b := L.dominantPullbackSectionCoefficient f hη 1
  have hs := (L.pullback f).rationalSectionChowClass_coefficient_independent (f ≫ gY) d hdX b
  have ht := L.rationalSectionChowClass_coefficient_independent gY d hd 1
  have hp := congrArg (Point.CycleChow.BundleCycles.pointCycleToChowQ gY d) (finitePushforward_lineBundleSection f hη gY L 1)
  rw [map_smul] at hp
  calc
    _ = Finite.ChowPushforward.BundleCycles.finiteChowPushforward f gY d
        (Point.CycleChow.BundleCycles.pointCycleToChowQ (f ≫ gY) d ((L.pullback f).rationalSectionPointCycleWithCoefficient b)) :=
      congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward f gY d) hs.symm
    _ = Point.CycleChow.BundleCycles.pointCycleToChowQ gY d (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f
        ((L.pullback f).rationalSectionPointCycleWithCoefficient b)) :=
      Finite.ChowPointClass.BundleCycles.finiteChowPushforward_pointClass f gY d _
    _ = (f.residueDegree (genericPoint X) : ℚ) • Point.CycleChow.BundleCycles.pointCycleToChowQ gY d
        (L.rationalSectionPointCycleWithCoefficient 1) := hp
    _ = _ := congrArg (fun z => (f.residueDegree (genericPoint X) : ℚ) • z) ht

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FiniteChowProjection.Cycles
