import OAI.RepresentationTheory.Theta.Geometric.GraphFormTrace
import OAI.RepresentationTheory.Theta.Geometric.Rational.FormsPullback

/-! # Central Form Trace -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The central Hecke operator on algebraic forms pulls back by the
actual marking shift, as follows from its graph correspondence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

def Data.ActiveHeckeThetaData.complexMarkingShift : D.pel.complexSpace ≅ D.pel.complexSpace :=
  (Over.pullback D.pel.complexGenericPoint).mapIso A.shift

include hA

theorem Data.ActiveHeckeThetaData.centralForms_markingShift (form : D.pel.OneFormsA) :
    D.pel.albanesePullback hg (D.pel.pullbackForms (A.integral (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)) form) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.complexMarkingShift A).hom (D.pel.albanesePullback hg form) := by
  obtain ⟨e, he, ht⟩ := hA.graph
  let F := Over.pullback D.pel.complexGenericPoint
  let C := D.pel.complexCorrespondence (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)
  have hs : C.source = (F.mapIso e).hom := congrArg F.map he.symm
  let : IsIso C.source := hs ▸ inferInstanceAs (IsIso (F.mapIso e).hom)
  let : IsIso C.source.left := inferInstanceAs (IsIso ((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).map C.source))
  have htarget : C.target = C.source ≫ (D.complexMarkingShift A).hom := by
    change F.map (D.pel.correspondence (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)).target =
      F.map (D.pel.correspondence (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)).source ≫ F.map A.shift.hom
    rw [ht, Functor.map_comp, he]
  exact GraphFormTrace.branchTrace_graph_pullback C (D.complexMarkingShift A).hom htarget
    (D.pel.albanesePullback hg form)
    (D.pel.albanesePullback hg (D.pel.pullbackForms (A.integral (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)) form))
    (hA.forms (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s) form)

theorem Data.ActiveHeckeThetaData.centralRationalForms_markingShift (form : D.pel.OneFormsA) :
    D.pel.albanesePullback hg (D.heckeRationalForms hg A (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)) form) =
      AlgebraicGeometry.AbelianScheme.TateComparison.FormConstants.formsPullback (D.complexMarkingShift A).hom (D.pel.albanesePullback hg form) := by
  change D.pel.albanesePullback hg
    (D.rationalFormsPullback hg (A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s))) form) = _
  have hi := hA.integral (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)
  change D.pel.toRational (A.integral (AlgebraicGeometry.AbelianScheme.TateComparison.Local.IntegralType.central s)) =
    A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)) at hi
  rw [← hi, D.rationalFormsPullback_integral]
  exact D.centralForms_markingShift hg hgood hIsogenyQuotient A hA form

end

end OAI.RepresentationTheory.Theta.Geometric
