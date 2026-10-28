import OAI.RepresentationTheory.Theta.Geometric.GlobalRationalBranchOccurrence
import OAI.RepresentationTheory.Theta.Geometric.Rational.CosetFaithfulness
import OAI.RepresentationTheory.Theta.Geometric.Cleared.BranchDegree

/-! # Active Branch Bijection -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original active inverse right cosets are in bijection with the
actual continuous cleared branches, with full rational target formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

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
theorem Data.ActiveHeckeThetaData.original_active_branch_bijection (a : Intrinsic.Hecke.ActiveWeight) :
    ∃ β : D.ClearedBranch (D.totalPeriodMap j X component cover) a ≃ Intrinsic.Hecke.activeCosets q a,
      ∀ b : D.ClearedBranch (D.totalPeriodMap j X component cover) a,
        ∃ g : D.RationalSU,
          (QuotientGroup.mk (D.activeLocal g)⁻¹ : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = (β b).val ∧
          D.away g ∈ D.awayLevel ∧
          ∀ x, D.clearedBranchTarget A.shift b x =
            D.totalPeriodMap j X component cover (D.rationalPeriodPoint g x) := by
  let c := D.totalPeriodMap j X component cover
  have hcont : Continuous c := D.totalPeriodMap_continuous j X component cover hcover.2.1.continuous
  let : Finite (D.ClearedBranch c a) := D.clearedBranch_finite hg hcont a
  choose g hcos haway htype using D.active_coset_rational_representative hArithmetic a
  choose B hB using fun k : Intrinsic.Hecke.activeCosets q a =>
    D.global_rational_cleared_branch hg hgood hIsogenyQuotient A hA hdegree hs hc
      j X component cover hcover href a (g k) (haway k) (htype k)
  have hBi : Function.Injective B := by
    intro k l hkl
    apply Subtype.ext
    calc
      k.val = QuotientGroup.mk (D.activeLocal (g k))⁻¹ := (hcos k).symm
      _ = QuotientGroup.mk (D.activeLocal (g l))⁻¹ :=
        D.rational_moduli_map_inverse_coset hg hc hgood hdegree (g k) (g l) (fun x => by
          rw [← href, ← href, ← hB k x, ← hB l x, hkl])
      _ = l.val := hcos l
  have hBij : Function.Bijective B := (Nat.bijective_iff_injective_and_card B).mpr
    ⟨hBi, (D.clearedBranch_card_eq_activeCosets hg hgood hIsogenyQuotient hdegree hs hcont a).symm⟩
  let e := Equiv.ofBijective B hBij
  refine ⟨e.symm, fun b => ⟨g (e.symm b), hcos _, haway _, ?_⟩⟩
  intro x
  have H := hB (e.symm b) x
  change D.clearedBranchTarget A.shift (e (e.symm b)) x = _ at H
  rwa [e.apply_symm_apply] at H

end

end OAI.RepresentationTheory.Theta.Geometric
