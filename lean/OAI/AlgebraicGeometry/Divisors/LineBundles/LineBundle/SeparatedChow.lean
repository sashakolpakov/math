import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.DVRApproximation
import OAI.AlgebraicGeometry.Divisors.LineBundles.SeparatedPointValuations
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.AffineMoving
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ProperResidueChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FinitePointProjection
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.ChowIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.ChowTransport

/-! # Separated Chow -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow.Cycles

/-! Prescribed orders at finitely many normal codimension-one points
of a separated integral scheme, using its actual function field. -/

open _root_.AlgebraicGeometry _root_.Order

theorem exists_separated_prescribed_orders {X : Scheme} [IsIntegral X]
    [IsLocallyNoetherian X] [X.IsSeparated]
    {ι : Type*} [Finite ι] (x : ι → X) (hx : ∀ i, coheight (x i) = 1)
    (hinj : Function.Injective x) [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))]
    (n : ι → ℤ) : ∃ g : X.functionFieldˣ, ∀ i, X.ord (g : X.functionField) (x i) = n i := by
  let : ∀ i, IsDiscreteValuationRing (X.presheaf.stalk (x i)) :=
    fun i => PositiveOrderIs.BundleCycles.PositiveOrder.stalk_isDVR (x i) (hx i)
  obtain ⟨g, hg⟩ := LineBundles.Finite.DVRApproximation.BundleCycles.exists_finiteDVR_prescribed_orders
    (fun i => X.presheaf.stalk (x i)) X.functionField
    (SeparatedPointValuations.BundleCycles.stalkAbsoluteValues_pairwise_inequivalent x hinj) n
  refine ⟨g, fun i => ?_⟩
  exact (X.ord_eq_ordHom_of_coheight_eq_one (hx i) _).trans (hg i)

end AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow.Cycles

namespace AlgebraicGeometry.Divisors.LineBundles

/-! # LineBundleCycles: moving line-bundle divisors on separated schemes -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_separated_rationalSection_avoiding_finitePoints {ι : Type*} [Finite ι]
    (x : ι → X) (hx : ∀ i, coheight (x i) = 1) (hinj : Function.Injective x)
    [∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))] :
    ∃ a : X.functionFieldˣ, ∀ i, L.rationalSectionPointDivisorWithCoefficient a (x i) = 0 := by
  obtain ⟨a, ha⟩ := LineBundle.SeparatedChow.Cycles.exists_separated_prescribed_orders x hx hinj
    (fun i => -L.rationalSectionOrder (x i))
  refine ⟨a, fun i => ?_⟩
  change X.ord (a : X.functionField) (x i) + L.rationalSectionOrder (x i) = 0
  rw [ha i, neg_add_cancel]

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_separated_rationalSection_avoiding_principalDivisor
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (g : X.functionField) :
    ∃ a : X.functionFieldˣ,
      Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g).support := by
  classical
  let S := (Ord.BundleCycles.principalDivisor X g).support
  have hx : ∀ x : S, coheight x.val = 1 := by
    intro x
    by_contra hc
    have hz : Ord.BundleCycles.principalDivisor X g x.val = 0 := X.ord_eq_zero_of_coheight_neq_one hc g
    exact (Finsupp.mem_support_iff.mp x.property) hz
  obtain ⟨a, ha⟩ := L.exists_separated_rationalSection_avoiding_finitePoints (fun x : S => x.val)
    hx Subtype.val_injective
  refine ⟨a, Finset.disjoint_left.mpr ?_⟩
  intro x hxA hxG
  exact (Finsupp.mem_support_iff.mp hxA) (ha ⟨x, hxG⟩)

theorem Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.exists_separated_rationalSection_class_avoiding_principalDivisor
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (g : X.functionField)
    (h : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType h] (d : ℕ)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension h = d + 1) :
    ∃ a : X.functionFieldˣ,
      Disjoint (L.rationalSectionPointDivisorWithCoefficient a).support (Ord.BundleCycles.principalDivisor X g).support ∧
      Point.CycleChow.BundleCycles.pointCycleToChowQ h d (L.rationalSectionPointCycleWithCoefficient a) = L.rationalSectionChowClass h d := by
  obtain ⟨a, ha⟩ := L.exists_separated_rationalSection_avoiding_principalDivisor g
  exact ⟨a, ha, L.rationalSectionChowClass_coefficient_independent h d hd a⟩

end AlgebraicGeometry.Divisors.LineBundles

namespace AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow.Cycles
open _root_.AlgebraicGeometry
open _root_.CategoryTheory
section

/-! # LineBundleCycles: line-bundle intersection kills every actual principal divisor on a normal separated scheme -/

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)

include hNormal hX in
theorem normalSeparatedLineBundlePointIntersection_principal_zero (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) = 0 := by
  let : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := hNormal
  obtain ⟨a, ha⟩ := L.exists_separated_rationalSection_avoiding_principalDivisor g.val
  exact ProperResidueChow.Cycles.lineBundlePointIntersection_principal_zero_of_proper L a g ha hNormal f d hX

include hNormal hX in
theorem normalSeparatedLineBundlePointIntersection_principal_nonzero (g : X.functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) = 0 :=
  normalSeparatedLineBundlePointIntersection_principal_zero L hNormal f d hX (Units.mk0 g hg)

end

section

/-! # LineBundleCycles: line-bundle intersection kills actual principal divisors on singular integral separated schemes -/

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X : Scheme.{0}} [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (d : ℕ) (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2)

include hX in
theorem separatedLineBundlePointIntersection_principal_zero (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g.val)) = 0 := by
  let N := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X
  let ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X
  let : IsFinite ν := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite X f
  let : AlgebraicGeometry.IsNoetherian N := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let : N.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from ν]
    infer_instance⟩
  let gN := NormalizationResidue.BundleCycles.normalizationFunctionUnit X g
  have hN : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (ν ≫ f) = d + 2 := (NormalizationResidue.BundleCycles.finiteNormalization_dimension X f).trans hX
  have hn := normalSeparatedLineBundlePointIntersection_principal_zero (L.pullback ν)
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_integrallyClosed X) (ν ≫ f) d hN gN
  have hdim : ∀ x : N, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor N gN.val x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (ν ≫ f) = d + 1 := by
    intro x hx
    have horder : Ord.BundleCycles.principalDivisor N gN.val x ≠ 0 := by
      intro hz
      apply hx
      change (Ord.BundleCycles.principalDivisor N gN.val x : ℚ) = 0
      rw [hz, Int.cast_zero]
    have hc := Normal.PointResidue.BundleCycles.principalDivisor_support_coheight N gN.val x (Finsupp.mem_support_iff.mpr horder)
    have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (ν ≫ f) x hc
    omega
  have hp := FinitePointProjection.Cycles.lineBundlePointIntersection_finite_projection ν f L d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor N gN.val) hdim
  have hz := congrArg (LineBundles.Finite.ChowPushforward.BundleCycles.finiteChowPushforward ν f d) hn
  rw [map_zero] at hz
  have he := hp.symm.trans hz
  have hg := NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X f g.val g.ne_zero
  exact (congrArg (fun z => Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L z)) hg).symm.trans he

include hX in
theorem separatedLineBundlePointIntersection_principal_nonzero (g : X.functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) = 0 :=
  separatedLineBundlePointIntersection_principal_zero L f d hX (Units.mk0 g hg)

end

section

/-! # LineBundleCycles: line-bundle intersection kills principal relations on every actual closed integral support -/

open _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem separatedLineBundlePointIntersection_supportPrincipal_zero (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L (Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g)) = 0 := by
  let Z := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  let : Z.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from i]
    infer_instance⟩
  have hn := separatedLineBundlePointIntersection_principal_nonzero (L.pullback i) (i ≫ f) d hW g hg
  have hdim : ∀ x : Z, RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g x ≠ 0 →
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d + 1 := by
    intro x hx
    have h := ChowIntersection.Cycles.rationalPrincipalPointDivisor_dimension Z (i ≫ f) g x hx
    change Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f at h
    omega
  have hp := FinitePointProjection.Cycles.lineBundlePointIntersection_finite_projection i f L d (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g) hdim
  have hz := congrArg (LineBundles.Finite.ChowPushforward.BundleCycles.finiteChowPushforward i f d) hn
  rw [map_zero] at hz
  have he := hp.symm.trans hz
  have hi : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward i (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Z g) =
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
    rw [IsomorphismDivisorPushforward.BundleCycles.pointPushforward_eq_mapDomain_of_immersion i]
    exact (Finsupp.embDomain_eq_mapDomain ⟨i, i.isClosedEmbedding.injective⟩ _).symm
  exact (congrArg (fun z => Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundlePointIntersection L z)) hi).symm.trans he

theorem separatedLineBundleCycleIntersection_principal_zero (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f (d + 1) W g)) = 0 := by
  rw [← Point.ChowTransport.BundleCycles.pointCycleToChowQ_inclusion, ← Intersection.Cycles.lineBundlePointIntersection_graded,
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f (d + 1) W (by omega)]
  exact separatedLineBundlePointIntersection_supportPrincipal_zero L f d W hW g hg

end

/-! # LineBundleCycles: actual line-bundle intersection descends to rational Chow on separated schemes -/

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [X.IsSeparated]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

theorem separatedLineBundleCycleIntersection_relations (d : ℕ) :
    DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1) ≤
      (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d).comap (Intersection.Cycles.lineBundleCycleIntersection L f d) := by
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨W, hW, g, hg, rfl⟩ := hz
  exact (DimensionChow.BundleCycles.dimensionCycleToChowQ_eq_zero_iff f d _).mp
    (separatedLineBundleCycleIntersection_principal_zero L f d W (by omega) g hg)

def separatedLineBundleChowIntersection (d : ℕ) : DimensionChow.BundleCycles.DimensionChowQ f (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d :=
  (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f (d + 1)).mapQ (DimensionChow.BundleCycles.dimensionRationalEquivalenceQ f d)
    (Intersection.Cycles.lineBundleCycleIntersection L f d) (separatedLineBundleCycleIntersection_relations L f d)

theorem separatedLineBundleChowIntersection_cycle (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    separatedLineBundleChowIntersection L f d (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) z) =
      DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z) := rfl

theorem separatedLineBundleChowIntersection_unique (d : ℕ)
    (T : DimensionChow.BundleCycles.DimensionChowQ f (d + 1) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ f d)
    (hT : ∀ z, T (DimensionChow.BundleCycles.dimensionCycleToChowQ f (d + 1) z) = DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Intersection.Cycles.lineBundleCycleIntersection L f d z)) :
    T = separatedLineBundleChowIntersection L f d := by
  ext α
  obtain ⟨z, rfl⟩ := DimensionChow.BundleCycles.dimensionCycleToChowQ_surjective f (d + 1) α
  exact hT z

end AlgebraicGeometry.Divisors.LineBundles.LineBundle.SeparatedChow.Cycles

end

end OAI
