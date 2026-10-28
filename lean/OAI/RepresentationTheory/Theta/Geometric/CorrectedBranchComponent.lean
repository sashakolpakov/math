import OAI.RepresentationTheory.Theta.Geometric.CorrectedCorrespondenceTrace
import OAI.RepresentationTheory.Theta.Geometric.PrincipalBranchStability
import OAI.RepresentationTheory.Theta.Geometric.Complex.ComponentLabels

/-! # Corrected Branch Component -/

namespace OAI.RepresentationTheory.Theta.Geometric.CorrectedBranchComponent

noncomputable section

/-! Actual corrected source-fiber branches preserve the principal
component indicator, with their exact algebraic endpoints. -/
set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
namespace ActiveHeckeThetaData
variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (A : TateComparison.Action D.pel)

local notation "generic" => OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.complexGenericPointEquiv (D := D)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.corrected_branch_generic_endpoint (a : Intrinsic.Hecke.ActiveWeight)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) (b : (D.correctedCorrespondence A a).Fiber x) :
    ∃ p : (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber (generic x),
      p.val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
        (fun z => z ≫ A.shift.hom)^[Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a]
          (generic ((D.correctedCorrespondence A a).endpoint b)) := by
  let C := D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)
  let p := C.baseChangeFiberEquiv D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) x b
  have he := C.baseChangeFiberEquiv_endpoint D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) x b
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a
  let f := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (D.complexMarkingShift A).hom
  let g := AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (D.complexMarkingShift A).inv
  have hi : Function.LeftInverse f g := by
    intro z
    change (z ≫ (D.complexMarkingShift A).inv) ≫ (D.complexMarkingShift A).hom = z
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hy : f^[n] ((D.correctedCorrespondence A a).endpoint b) =
      b.val ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target := by
    change f^[n] (b.val ≫ ((D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target ≫
      IteratedSchemePullback.schemeEndPower (D.complexMarkingShift A).inv n)) = _
    rw [← Category.assoc]
    change f^[n] (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (IteratedSchemePullback.schemeEndPower (D.complexMarkingShift A).inv n) _) = _
    rw [IteratedSchemePullback.schemeEndPower_complexPoints]
    exact hi.iterate n _
  refine ⟨p, ?_⟩
  have H := congrArg generic hy
  exact he.symm.trans (H.symm.trans
    (D.complexGenericPointEquiv_iterate A.shift n ((D.correctedCorrespondence A a).endpoint b)))

variable [IsTopologicalGroup Ga]
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates) (hArithmetic : DenseRange D.rationalFinite)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover)
    (href : ∀ x, D.totalPeriodMap j X component cover x = D.referenceModuliMap hg x)

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.corrected_branch_component_iff (a : Intrinsic.Hecke.ActiveWeight)
    (i k : Fin D.pel.componentCount)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex i)) (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (D.componentComplex k))
    (b : (D.correctedCorrespondence A a).Fiber (x ≫ D.componentComplexInclusion i))
    (hb : (D.correctedCorrespondence A a).endpoint b = y ≫ D.componentComplexInclusion k) :
    i = j ↔ k = j := by
  have hp := D.corrected_branch_generic_endpoint A a (x ≫ D.componentComplexInclusion i) b
  rw [hb] at hp
  constructor
  · intro hi
    subst i
    obtain ⟨z, hz⟩ := (D.periodImage_component_iff j X component cover hcover.1 _).mpr ⟨x, rfl⟩
    rw [hz] at hp
    obtain ⟨w, hw⟩ := D.cleared_neighbor_outgoing hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
      j X component cover hcover href a z (y ≫ D.componentComplexInclusion k) hp
    obtain ⟨v, hv⟩ := (D.periodImage_component_iff j X component cover hcover.1 _).mp ⟨w, hw⟩
    exact D.component_complex_point_label hg y v hv.symm
  · intro hk
    subst k
    obtain ⟨z, hz⟩ := (D.periodImage_component_iff j X component cover hcover.1 _).mpr ⟨y, rfl⟩
    rw [hz] at hp
    obtain ⟨w, hw⟩ := D.cleared_neighbor_incoming hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
      j X component cover hcover href a (x ≫ D.componentComplexInclusion i) z hp
    obtain ⟨v, hv⟩ := (D.periodImage_component_iff j X component cover hcover.1 _).mp ⟨w, hw⟩
    exact D.component_complex_point_label hg x v hv.symm

end ActiveHeckeThetaData

end

end OAI.RepresentationTheory.Theta.Geometric.CorrectedBranchComponent
