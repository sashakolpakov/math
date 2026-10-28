import OAI.RepresentationTheory.Theta.Geometric.Cleared.PELType
import OAI.RepresentationTheory.Theta.Geometric.TypedIsogenyBranch
import OAI.RepresentationTheory.Theta.Geometric.Active.RationalClearing
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices

/-! # Coset Fiber Branch -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every prescribed active rational representative occurs pointwise
in the actual TateComparison correspondence, with its literal central-shifted target. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem Active.CosetFiberBranch.clearedActiveType_multiplierNat {s : ℕ} (v : Fin s) (a : Intrinsic.Hecke.ActiveWeight) :
    (Intrinsic.Hecke.clearedActiveType v a).multiplierNat = 2 * Intrinsic.Hecke.clearingExponent v a := by
  change (0 + 2 * (Intrinsic.Hecke.clearingExponent v a : ℤ)).toNat = _
  omega

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
theorem Data.ActiveHeckeThetaData.active_rational_original_fiber_branch
    (a : Intrinsic.Hecke.ActiveWeight) (g : D.RationalSU) (haway : D.away g ∈ D.awayLevel)
    (hcos : DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q)
      (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹ (D.activeLocal g)⁻¹)
    (x : D.domain) (R : D.ReferencePELPointData hg x)
    (S : D.ReferencePELPointData hg (D.rationalPeriodPoint g x)) :
    ∃ c : (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber R.genericPoint,
      c.val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
        (fun z => z ≫ A.shift.hom)^[Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a] S.genericPoint := by
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a
  let t := Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a
  have hn := D.active_doubleCoset_exact_clearing hg hc hgood hdegree a g haway hcos
  obtain ⟨e, _, he⟩ := D.exists_cleared_reference_PEL_isogeny hg hc hgood g haway n hn x R S
  let frame := R.genericTateFrame hgood hdegree
  have hf := R.genericTateFrame_isSplitAction hgood hdegree hc
  have hi : ∃ i : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint)
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint)
        ((fun z => z ≫ A.shift.hom)^[n] S.genericPoint)) (q ^ t.multiplierNat),
      ∀ v, ∃ L : AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RankThreeLattice ℤ_[q] ℚ_[q],
        AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice frame i.isogeny.hom (v, false) = L.val ∧
        AlgebraicGeometry.AbelianScheme.TateComparison.Duality.RelativePosition (q : ℤ_[q]) (t.val.exponent v)
          (D.pel.framedFiberSourceLattice (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint)
            R.genericPoint frame (v, false)) L := by
    change ∃ i : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny _ _ (q ^ (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a).multiplierNat), _
    rw [Active.CosetFiberBranch.clearedActiveType_multiplierNat]
    refine ⟨Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny R S hgood hIsogenyQuotient A hA n e, ?_⟩
    intro v
    refine ⟨Data.ActiveHeckeThetaData.clearedLocalInverseLattice g n (v, false),
      Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny_lattice R S hgood hdegree hc g n e he hIsogenyQuotient A hA _, ?_⟩
    rw [R.genericTateFrame_sourceLattice hgood hdegree hc]
    exact D.clearedLocalInverseLattice_relativePosition hc a g haway hcos v
  obtain ⟨i, hi⟩ := hi
  exact TypedIsogenyBranch.exists_original_branch_of_typed_isogeny D.pel hg hgood hIsogenyQuotient hdegree hs
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Lattices.Intrinsic.verifiedElementaryDivisors ℤ_[q] ℚ_[q]) R.genericPoint _ frame hf t i hi

end

end OAI.RepresentationTheory.Theta.Geometric
