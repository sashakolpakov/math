import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PrincipalChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Chow Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowIntersection.Cycles

noncomputable section

section

/-! # LineBundleCycles: line-bundle intersection kills principal relations on every actual closed integral support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem rationalPrincipalPointDivisor_dimension (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (g : X.functionField) (x : X)
    (hx : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have horder : Ord.BundleCycles.principalDivisor X g x ≠ 0 := by
    intro hz
    apply hx
    change (Ord.BundleCycles.principalDivisor X g x : ℚ) = 0
    rw [hz, Int.cast_zero]
  exact DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one f x
    (Normal.PointResidue.BundleCycles.principalDivisor_support_coheight X g x (Finsupp.mem_support_iff.mpr horder))

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    {fY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y fY) (q : X ⟶ Y) [IsAffineHom q]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include P q in
theorem lineBundlePointIntersection_supportPrincipal_zero (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0 := by
  let Z := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  have hn := PrincipalChow.Cycles.lineBundlePointIntersection_principal_nonzero P (i ≫ q) (L.pullback i) (i ≫ f) d hW g hg
  have hdim : ∀ x : Z, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d + 1 := by
    intro x hx
    have h := rationalPrincipalPointDivisor_dimension Z (i ≫ f) g x hx
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f at h
    omega
  have hp := FinitePointProjection.Cycles.lineBundlePointIntersection_finite_projection i f L d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g) hdim
  have hz := congrArg (Finite.ChowPushforward.BundleCycles.finiteChowPushforward i f d) hn
  rw [map_zero] at hz
  have he := hp.symm.trans hz
  have hi : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
    rw [IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion i]
    exact (Finsupp.embDomain_eq_mapDomain ⟨i, i.isClosedEmbedding.injective⟩ _).symm
  exact (congrArg (fun z => Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L z)) hi).symm.trans he

include P q in
theorem lineBundleCycleIntersection_principal_zero (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f (d + 1) W g)) = 0 := by
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion, ← Intersection.Cycles.lineBundlePointIntersection_graded,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f (d + 1) W (by omega)]
  exact lineBundlePointIntersection_supportPrincipal_zero P q L f d W hW g hg

end

/-! # LineBundleCycles: actual line-bundle intersection descends to rational Chow on schemes affine over projective schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    {fY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y fY) (q : X ⟶ Y) [IsAffineHom q]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include P q in
theorem lineBundleCycleIntersection_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1) ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).comap (Intersection.Cycles.lineBundleCycleIntersection L f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d _).mp
    (lineBundleCycleIntersection_principal_zero P q L f d W (by omega) g hg)

def lineBundleChowIntersection (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1)).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d)
    (Intersection.Cycles.lineBundleCycleIntersection L f d) (lineBundleCycleIntersection_relations P q L f d)

theorem lineBundleChowIntersection_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    lineBundleChowIntersection P q L f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z) := rfl

theorem lineBundleChowIntersection_unique (d : ℕ)
    (T : DimensionChow.BundleCycles.DimensionChowQ f (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d)
    (hT : ∀ z, T (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) z) = DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z)) :
    T = lineBundleChowIntersection P q L f d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f (d + 1) α
  exact hT z

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowIntersection.Cycles
