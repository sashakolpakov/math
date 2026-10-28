import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowTransport
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage

/-! # Generic Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass.Cycles

noncomputable section

/-! Intersecting the actual fundamental generic-point cycle of an
integral scheme gives the line bundle's constructed rational-section class. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (X : Scheme.{0}) [IsIntegral X]

instance genericPointSupport_isIso : IsIso (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (genericPoint X))) := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (genericPoint X))
  have hr : Set.range j = Set.univ := (CycleClass.Geometric.GenericPoint.range_reducedSupportι _).trans (genericPoint_spec X).def
  let : Surjective j := ⟨Set.range_eq_univ.mp hr⟩
  exact isIso_of_isClosedImmersion_of_surjective j

theorem genericPointSupport_dimension (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (genericPoint X)) f =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have hp : CycleClass.Geometric.StratumClosure.integralImageClosure (𝟙 X) = irreducibleSetEquivPoints.symm (genericPoint X) := by
    apply irreducibleSetEquivPoints.injective
    rw [Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint, irreducibleSetEquivPoints.apply_symm_apply]
    rfl
  have hd := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (𝟙 X) f
  rw [Category.id_comp, hp] at hd
  exact hd.symm

variable [AlgebraicGeometry.IsNoetherian X] (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem lineBundleGenericDivisor_class (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L (irreducibleSetEquivPoints.symm (genericPoint X))) =
      L.rationalSectionChowClass f d := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (genericPoint X))
  have h := L.iso_pushforward_chowClass (asIso j) f d hd
  change Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d (Point.CycleChow.BundleCycles.pointCycleToChowQ (j ≫ f) d (L.pullback j).rationalSectionPointCycle) = _ at h
  rw [Closed.ChowPointClass.BundleCycles.closedChowPushforward_pointClass] at h
  exact h

theorem separatedLineBundleChowIntersection_generic [X.IsSeparated]
    (d : ℕ) (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 1) :
    SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d (Point.CycleChow.BundleCycles.pointCycleToChowQ f (d + 1) (Finsupp.single (genericPoint X) 1)) =
      L.rationalSectionChowClass f d := by
  let x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) := ⟨genericPoint X, (genericPointSupport_dimension X f).trans hd⟩
  change SeparatedChow.Cycles.separatedLineBundleChowIntersection L f d
    (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) (Finite.ChowPointClass.BundleCycles.schemeDimensionComponent f (d + 1) (Finsupp.single x.val 1))) = _
  rw [Finite.ChowPointClass.BundleCycles.schemeDimensionComponent_single f (d + 1) x, SeparatedChow.Cycles.separatedLineBundleChowIntersection_cycle,
    Intersection.Cycles.lineBundleCycleIntersection_single, one_smul]
  exact lineBundleGenericDivisor_class X L f d hd

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GenericClass.Cycles
