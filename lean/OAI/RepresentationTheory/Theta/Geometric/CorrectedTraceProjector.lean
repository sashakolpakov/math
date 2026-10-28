import OAI.RepresentationTheory.Theta.Geometric.CorrectedBranchComponent
import OAI.RepresentationTheory.Theta.Geometric.BallFormsProjector
import OAI.RepresentationTheory.Theta.Geometric.Dual.TestFormFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.AlbaneseFormFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.ComponentVarieties
import OAI.RepresentationTheory.Theta.Geometric.Dual.BranchSplitting

/-! # Corrected Trace Projector -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual corrected trace commutes with the original component
projector on every dual-number test, and hence on all algebraic forms. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates) (hArithmetic : DenseRange D.rationalFinite)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (href : ∀ x, D.totalPeriodMap j X component cover x = D.referenceModuliMap hg x)

include hA hdegree hs hc hArithmetic hcover href in
theorem Data.ActiveHeckeThetaData.corrected_branch_projector_value (a : Intrinsic.Hecke.ActiveWeight) (i : Fin D.pel.componentCount)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ D.componentComplex i)
    (d : (D.correctedCorrespondence A a).Fiber (t ≫ D.componentComplexInclusion i))
    (ω : D.pel.OneFormsA) :
    (D.pel.albanesePullback hg (D.ballFormsProjector j ω)).val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
      ((D.correctedCorrespondence A a).endpoint d) =
    if i = j then (D.pel.albanesePullback hg ω).val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
      ((D.correctedCorrespondence A a).endpoint d) else 0 := by
  let C := D.correctedCorrespondence A a
  obtain ⟨k, l, hl⟩ := D.dualTest_component_lift hg (C.endpoint d)
  let b : C.Fiber ((AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t) ≫ D.componentComplexInclusion i) :=
    ⟨AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ d.val, by rw [Category.assoc, d.property, ← Category.assoc]⟩
  have hb : C.endpoint b = (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ l) ≫ D.componentComplexInclusion k := by
    have H := congrArg (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ ·) hl.symm
    simpa only [b, AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence.endpoint, Category.assoc] using H
  have hlabel := D.corrected_branch_component_iff A hg hgood hIsogenyQuotient hA hdegree hs hc hArithmetic
    j X component cover hcover href a i k (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ t) (AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualClosedPoint ≫ l) b hb
  have H := congrArg (fun η : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms (D.componentComplex k) => η.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest l)
    (D.ballFormsProjector_component hg k j ω)
  change (D.pel.albanesePullback hg (D.ballFormsProjector j ω)).val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest
    (l ≫ D.componentComplexInclusion k) = _ at H
  rw [hl] at H
  by_cases hij : i = j
  · have hkj : k = j := hlabel.mp hij
    simp only [hij, ite_true]
    simp only [hkj, ite_true] at H
    change (D.pel.albanesePullback hg (D.ballFormsProjector j ω)).val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (C.endpoint d) =
      (D.pel.albanesePullback hg ω).val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (l ≫ D.componentComplexInclusion k) at H
    rwa [hl] at H
  · have hkj : k ≠ j := fun h => hij (hlabel.mpr h)
    simp only [hij, ite_false]
    simp only [hkj, ite_false] at H
    exact H

include hA hdegree hs hc hArithmetic hcover href in
theorem Data.ActiveHeckeThetaData.activeForms_projector_dualTest (a : Intrinsic.Hecke.ActiveWeight) (i : Fin D.pel.componentCount)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.affineComplexTest AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest ⟶ D.componentComplex i) (ω : D.pel.OneFormsA) :
    (D.pel.albanesePullback hg
      (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) (D.ballFormsProjector j ω))).val
      AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (t ≫ D.componentComplexInclusion i) =
    if i = j then
      (D.pel.albanesePullback hg
        (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ω)).val
        AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (t ≫ D.componentComplexInclusion i) else 0 := by
  let C := D.correctedCorrespondence A a
  let u := t ≫ D.componentComplexInclusion i
  obtain ⟨n, ⟨e⟩⟩ := Dual.BranchSplitting.exists_dualBranchSplitting C u
  rw [D.activeForms_corrected_trace A hg hgood hIsogenyQuotient hA a (D.ballFormsProjector j ω) AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest u n e]
  simp_rw [D.corrected_branch_projector_value hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href a i t]
  by_cases hij : i = j
  · simp only [hij, ite_true]
    exact (D.activeForms_corrected_trace A hg hgood hIsogenyQuotient hA a ω AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest u n e).symm
  · simp only [hij, ite_false, Finset.sum_const_zero]

include hA hdegree hs hc hArithmetic hcover href in
theorem Data.ActiveHeckeThetaData.activeForms_projector_commute (a : Intrinsic.Hecke.ActiveWeight) :
    (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a))).comp
      (D.ballFormsProjector j) =
    (D.ballFormsProjector j).comp
      (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a))) := by
  apply LinearMap.ext
  intro ω
  apply D.albanesePullback_injective hg
  apply D.componentForms_jointly_injective hg
  intro i
  let V := D.componentVariety hg i
  let e := D.componentVarietyIso hg i
  have hinj : Function.Injective (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.hom) := by
    intro α β h
    have H := congrArg (AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback e.inv) h
    simpa only [← LinearMap.comp_apply, ← AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_comp, Iso.inv_hom_id, AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback_id,
      LinearMap.id_apply] using H
  apply hinj
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  apply Dual.TestFormFaithfulness.oneForms_eq_of_dualTests V.toOver
  intro t
  have H := D.activeForms_projector_dualTest hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href a i (t ≫ e.hom) ω
  have P := congrArg (fun η : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms (D.componentComplex i) => η.val AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJet.dualTest (t ≫ e.hom))
    (D.ballFormsProjector_component hg i j
      (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ω))
  by_cases hij : i = j
  · simp only [hij, ite_true] at H P
    exact congrArg AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (H.trans P.symm)
  · simp only [hij, ite_false] at H P
    exact congrArg AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodJetDifferentials.dualDifferential (H.trans P.symm)

end

end OAI.RepresentationTheory.Theta.Geometric
