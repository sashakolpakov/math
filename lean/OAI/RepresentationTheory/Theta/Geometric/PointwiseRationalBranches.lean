import OAI.RepresentationTheory.Theta.Geometric.Active.CosetFiberBranch
import OAI.RepresentationTheory.Theta.Geometric.GenericClearedBranchTargets

/-! # Pointwise Rational Branches -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every original rational coset target is attained pointwise by an
actual continuous cleared branch, with the literal original period map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    (hc : D.HasFiniteCoordinates)

include hA hdegree hs hc in
theorem Data.ActiveHeckeThetaData.pointwise_rational_cleared_branch
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hcont : Continuous c)
    (href : ∀ x, c x = D.referenceModuliMap hg x)
    (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹)
    (x : D.domain) :
    ∃ b : D.ClearedBranch c a, D.clearedBranchTarget A.shift b x = c (D.rationalPeriodPoint g x) := by
  have heq : c = D.referenceModuliMap hg := funext href
  subst c
  apply D.exists_clearedBranch_of_generic_endpoint hg hcont A.shift a x
    (D.referenceModuliMap hg (D.rationalPeriodPoint g x))
  exact D.active_rational_original_fiber_branch hg hgood hIsogenyQuotient A hA hdegree hs hc
    a g haway hcos x (D.referencePELPointData hg x)
      (D.referencePELPointData hg (D.rationalPeriodPoint g x))

end

end OAI.RepresentationTheory.Theta.Geometric
