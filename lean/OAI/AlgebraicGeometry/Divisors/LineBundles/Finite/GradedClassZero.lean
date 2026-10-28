import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedOverPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.CycleClassZero
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.GradedAbsoluteClass

/-! # Graded Class Zero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedClassZero.BundleCycles

noncomputable section

/-! The canonical graded class of a finite residue-weighted pushforward
vanishes whenever the class of the original finite cycle vanishes. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ProperSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.MapDimension.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
    [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)]
    [IsIntegral Y.left] [Smooth Y.hom]
    [AlgebraicGeometry.IsNoetherian Y.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
    (f : X ⟶ Y) [IsFinite f.left]

theorem schemeAbsoluteCycleClass_congrSupport (C D : IrreducibleCloseds X.left) (h : C = D) (p : ℕ)
    (hc : Foundations.Scheme.SupportDimension.supportTranscendenceDimension C X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension D X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom) :
    Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X C p hc = Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X D p hd := by
  subst D
  rfl

theorem finiteOverGradedClass_zero (d p q : ℕ)
    (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hq : d + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)
    (hzero : Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hp a = 0) :
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d q hq (GradedOverPushforward.BundleCycles.finiteOverGradedPushforward f d a) = 0 := by
  classical
  let Z : a.support → IrreducibleCloseds X.left := fun x => irreducibleSetEquivPoints.symm x.val.val
  have hZ (i : a.support) : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z i) X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom :=
    (congrArg (fun k => k + p) i.val.property).trans hp
  have hB (i : a.support) : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) Y.hom + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom :=
    (congrArg (fun k => k + q) ((CycleClass.Thom.Integral.MapDimension.Constructions.finite_support_dimension f (Z i)).trans i.val.property)).trans hq
  have hs : a = ∑ i : a.support, Finsupp.single i.val (a i.val) :=
    a.sum_single.symm.trans (Finset.sum_coe_sort a.support (fun x => Finsupp.single x (a x))).symm
  have hsource : ∑ i : a.support, a i.val • Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass X (Z i) p (hZ i) = 0 := by
    have h := congrArg (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass X d p hp) hs
    rw [map_sum] at h
    exact (Finset.sum_congr rfl (fun i _ => (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single X d p hp i.val (a i.val)).symm)).trans
      (h.symm.trans hzero)
  have hdegX : 2 * p + 2 * d = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom := by
    have h := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension X.hom
    omega
  have hdegY : 2 * q + 2 * d = 2 * Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom := by
    have h := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension Y.hom
    omega
  have hz := CycleClassZero.BundleCycles.finiteCycleClass_zero_of_source_zero f Z p q hZ hB (fun i => a i.val) hsource (2 * d) hdegX hdegY
  have ht : Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass Y d q hq (GradedOverPushforward.BundleCycles.finiteOverGradedPushforward f d a) =
      ∑ i : a.support, a i.val • ((f.left.residueDegree (irreducibleSetEquivPoints (Z i)) : ℚ) •
        Scheme.AbsoluteCycleClass.BundleCycles.schemeAbsoluteCycleClass Y (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i)) q (hB i)) := by
    conv_lhs => rw [hs, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [GradedOverPushforward.BundleCycles.finiteOverGradedPushforward_single, Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_single, mul_smul]
    have he := schemeAbsoluteCycleClass_congrSupport
      (irreducibleSetEquivPoints.symm (GradedOverPushforward.BundleCycles.finiteOverDimensionPoint f d i.val).val) (CycleClass.Thom.Scheme.ProperSupport.Constructions.imageSupport f (Z i))
      (GradedOverPushforward.BundleCycles.finiteOverDimensionPoint_support f d i.val) q
      ((congrArg (fun k => k + q) (GradedOverPushforward.BundleCycles.finiteOverDimensionPoint f d i.val).property).trans hq) (hB i)
    change a i.val • ((f.left.residueDegree i.val.val : ℚ) • _) = _
    have hpoint : irreducibleSetEquivPoints (Z i) = i.val.val := OrderIso.apply_symm_apply _ _
    rw [hpoint]
    exact congrArg (fun t => a i.val • ((f.left.residueDegree i.val.val : ℚ) • t)) he
  exact ht.trans hz

theorem finiteOverGradedCycleClass_zero (d p q : ℕ)
    (hp : d + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom)
    (hq : d + q = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom)
    (a : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint X.hom d →₀ ℚ)
    (hzero : Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass X d p hp a = 0) :
    Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedCycleClass Y d q hq (GradedOverPushforward.BundleCycles.finiteOverGradedPushforward f d a) = 0 :=
  (Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_zero_iff Y d q hq _).mp
    (finiteOverGradedClass_zero f d p q hp hq a ((Scheme.GradedAbsoluteClass.BundleCycles.schemeGradedAbsoluteCycleClass_zero_iff X d p hp a).mpr hzero))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GradedClassZero.BundleCycles
