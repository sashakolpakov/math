import OAI.RepresentationTheory.Theta.Geometric.Active.FormClearing
import OAI.RepresentationTheory.Theta.Geometric.IteratedSchemePullback

/-! # Corrected Correspondence Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The active rational operator is the original algebraic branch trace
with the literal inverse marking shift composed into its target map. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (A : TateComparison.Action D.pel)

def Data.ActiveHeckeThetaData.correctedCorrespondence (a : Intrinsic.Hecke.ActiveWeight) : AlgebraicGeometry.AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence D.pel.complexSpace where
  cover := (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover
  source := (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source
  target := (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target ≫
    IteratedSchemePullback.schemeEndPower (D.complexMarkingShift A).inv (Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a)
  finite := (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).finite
  etale := (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).etale

variable (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

include hA in
theorem Data.ActiveHeckeThetaData.activeForms_corrected_trace (a : Intrinsic.Hecke.ActiveWeight) (ω : D.pel.OneFormsA) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Branches.IsBranchTrace (D.correctedCorrespondence A a) (D.pel.albanesePullback hg ω)
      (D.pel.albanesePullback hg
        (D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ω)) := by
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a
  let u := hA.centralUnit.unit
  have hu : (u : D.pel.EndQ) = A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)) := hA.centralUnit.unit_spec
  let shifted := D.rationalFormsPullback hg ((↑u⁻¹ : D.pel.EndQ) ^ n) ω
  have hshift : D.pel.albanesePullback hg shifted =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (IteratedSchemePullback.schemeEndPower (D.complexMarkingShift A).inv n) (D.pel.albanesePullback hg ω) :=
    (D.centralInverseForms_power_markingShift hg hgood hIsogenyQuotient A hA u hu n ω).trans
      (IteratedSchemePullback.formsPullback_schemeEndPower (D.complexMarkingShift A).inv n (D.pel.albanesePullback hg ω)).symm
  have hactive := congrArg (fun F : Module.End ℂ D.pel.OneFormsA => F ω)
    (D.activeForms_clearing hg hgood hIsogenyQuotient A hA u hu a)
  change D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished a)) ω =
    D.pel.pullbackForms (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)) shifted at hactive
  intro R t m e
  rw [hactive, hA.forms (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a) shifted R t m e]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg (fun η : AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.OneForms D.pel.complexSpace => η.val R
    ((D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).endpoint
      ((D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).splitBranch t e i))) hshift
  exact h.trans (congrArg (fun f => (D.pel.albanesePullback hg ω).val R f) (Category.assoc _ _ _))

end

end OAI.RepresentationTheory.Theta.Geometric
