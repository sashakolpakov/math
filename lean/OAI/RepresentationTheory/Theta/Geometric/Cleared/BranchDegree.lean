import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BranchLattices
import OAI.RepresentationTheory.Theta.Geometric.Active.DoubleCosetFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices

/-! # Branch Degree -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The number of actual continuous cleared branches is exactly the raw
SL3 double-coset degree. The central clearing contributes no multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices.Construction

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.clearedBranch_card_eq_activeCosets (hg : D.pel.HasIntegralModelGeometry)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient)
    (hdegree : Module.finrank ℚ E = 2 * s) (hs : 0 < s)
    {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace} (hc : Continuous c)
    (a : Intrinsic.Hecke.ActiveWeight) : Nat.card (D.ClearedBranch c a) = Nat.card (Intrinsic.Hecke.activeCosets q a) := by
  let x₀ := D.domainOrigin hg
  let t := Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a
  let b := 𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint
  let x := D.branchGenericPoint c x₀
  have hcast (v : Fin s) : (fun i => (t.exponentNat v i : ℤ)) = t.val.exponent v := by
    funext i
    exact t.exponentNat_cast v i
  let e : (D.pel.correspondence t).Fiber x ≃
      (∀ v : Fin s, AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q (t.val.exponent v))) := by
    refine (D.pel.geometricFiberRawCosetEquiv hgood hdegree hs hg b x hIsogenyQuotient t).trans
      (Equiv.piCongrRight fun v => ?_)
    exact Equiv.cast (congrArg (fun a : Fin 3 → ℤ =>
      ↥(AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Hecke.Construction.rawRightCosetSupport (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockLatticeCosets.Construction.blockIntegralLevel q) (AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.blockDiagonal q a))) (hcast v))
  exact Nat.card_congr
    (((D.nativeClearedBranchGenericFiberEquiv hg hc a x₀).trans e).trans
      ((AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SplitHeckeChoices.Construction.splitRawBlockSupportEquiv s q t.val).symm.trans
        (Active.DoubleCosetFibers.Spherical.clearedActiveSupportCosetEquiv q D.pel.reference.distinguished a)))

end

end OAI.RepresentationTheory.Theta.Geometric
