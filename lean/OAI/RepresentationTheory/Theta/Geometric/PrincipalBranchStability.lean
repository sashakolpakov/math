import OAI.RepresentationTheory.Theta.Geometric.Reference.ActiveBranchBijection
import OAI.RepresentationTheory.Theta.Geometric.ReverseClearedBranch

/-! # Principal Branch Stability -/

namespace OAI.RepresentationTheory.Theta.Geometric.PrincipalBranchStability.ActiveHeckeThetaData

noncomputable section

/-! The original cleared correspondences preserve the period component
in both directions, including their actual generic endpoints. -/
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

local notation "c" => D.totalPeriodMap j X component cover
local notation "generic" => OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.complexGenericPointEquiv (D := D)

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.cleared_neighbor_outgoing (a : Intrinsic.Hecke.ActiveWeight) (x : D.domain)
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (hp : ∃ p : (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber (generic (c x)),
      p.val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
        (fun z => z ≫ A.shift.hom)^[Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a] (generic y)) :
    ∃ z : D.domain, y = c z := by
  have hcont := D.totalPeriodMap_continuous j X component cover hcover.2.1.continuous
  obtain ⟨b, hb⟩ := D.exists_clearedBranch_of_generic_endpoint hg hcont A.shift a x y hp
  obtain ⟨β, hβ⟩ := D.original_active_branch_bijection hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href a
  obtain ⟨g, _, _, hg'⟩ := hβ b
  exact ⟨D.rationalPeriodPoint g x, hb.symm.trans (hg' x)⟩

include hA hdegree hs hc hArithmetic hcover href in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.cleared_neighbor_incoming (a : Intrinsic.Hecke.ActiveWeight)
    (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) (y : D.domain)
    (hp : ∃ p : (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber (generic x),
      p.val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
        (fun z => z ≫ A.shift.hom)^[Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a] (generic (c y))) :
    ∃ z : D.domain, x = c z := by
  obtain ⟨p, hp⟩ := hp
  have hr := ReverseClearedBranch.reverse_cleared_branch D.pel hg hgood hIsogenyQuotient A hA hdegree hs a
    (generic x) (generic (c y)) p hp
  exact D.cleared_neighbor_outgoing hg hgood hIsogenyQuotient A hA hdegree hs hc hArithmetic
    j X component cover hcover href (ReverseActiveWeight.reverseActiveWeight a) y x hr

end

end OAI.RepresentationTheory.Theta.Geometric.PrincipalBranchStability.ActiveHeckeThetaData
