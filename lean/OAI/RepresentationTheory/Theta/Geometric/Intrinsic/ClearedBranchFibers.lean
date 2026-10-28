import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CorrespondenceCovering
import OAI.RepresentationTheory.Theta.Geometric.Cleared.BranchFibers

/-! # Cleared Branch Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Original cleared branches are exactly one actual algebraic source
fiber, with the required covering property proved from IntegralModel geometry. -/

open _root_.CategoryTheory

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

def Data.ActiveHeckeThetaData.nativeClearedBranchFiberEquiv (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) (x₀ : D.domain) : D.ClearedBranch c a ≃
    {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover //
      p ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source = c x₀} :=
  D.clearedBranchFiberEquiv hg hc a (D.correspondenceSource_isCoveringMap hg _) x₀

theorem Data.ActiveHeckeThetaData.nativeClearedBranchFiberEquiv_apply (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) (x₀ : D.domain) (b : D.ClearedBranch c a) :
    (D.nativeClearedBranchFiberEquiv hg hc a x₀ b).val = b.lift x₀ := rfl

theorem Data.ActiveHeckeThetaData.clearedBranch_finite (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) : Finite (D.ClearedBranch c a) := by
  let x₀ := D.domainOrigin hg
  let F := {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
    (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover //
    p ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source = c x₀}
  have : Finite F := (D.correspondenceSource_finite_fiber hg _ (c x₀)).to_subtype
  exact Finite.of_equiv F (D.nativeClearedBranchFiberEquiv hg hc a x₀).symm

theorem Data.ActiveHeckeThetaData.clearedBranch_eq_of_value (hg : D.pel.HasIntegralModelGeometry)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    {a : Intrinsic.Hecke.ActiveWeight} (x₀ : D.domain) (b d : D.ClearedBranch c a)
    (h : b.lift x₀ = d.lift x₀) : b = d :=
  (D.nativeClearedBranchFiberEquiv hg hc a x₀).injective (Subtype.ext h)

theorem Data.ActiveHeckeThetaData.totalPeriodMap_continuous (j : Fin D.pel.componentCount)
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (component : X.toOver ≅ D.componentComplex j)
    (cover : D.domain → X.analyticSpace) (hc : Continuous cover) :
    Continuous (D.totalPeriodMap j X component cover) :=
  (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (component.hom ≫ D.componentComplexInclusion j)).comp hc

def Data.ActiveHeckeThetaData.periodClearedBranchFiberEquiv (hg : D.pel.HasIntegralModelGeometry)
    (j : Fin D.pel.componentCount) (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (component : X.toOver ≅ D.componentComplex j) (cover : D.domain → X.analyticSpace)
    (hcover : D.IsPeriodUniformization X cover) (a : Intrinsic.Hecke.ActiveWeight) :
    D.ClearedBranch (D.totalPeriodMap j X component cover) a ≃
    {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints
      (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).cover //
      p ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).source =
        D.totalPeriodMap j X component cover (D.domainOrigin hg)} :=
  D.nativeClearedBranchFiberEquiv hg
    (D.totalPeriodMap_continuous j X component cover hcover.2.1.continuous) a (D.domainOrigin hg)

end

end OAI.RepresentationTheory.Theta.Geometric
