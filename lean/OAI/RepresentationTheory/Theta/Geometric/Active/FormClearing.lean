import OAI.RepresentationTheory.Theta.Geometric.InverseCentralFormPowers
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution

/-! # Form Clearing -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Raw central clearing expresses an active rational pullback as the
original integral correspondence acting on the inverse-shifted form. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
    (hg : D.pel.HasIntegralModelGeometry) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient)

include hA

theorem Data.ActiveHeckeThetaData.realizedBasis_eq_sphericalBasis (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s) :
    A.basis t = AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.sphericalBasis s q t :=
  AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.rawDoubleCoset_unique (AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.integralLevel s q) (hA.basis t) (AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.sphericalBasis_isRaw s q t)

theorem Data.ActiveHeckeThetaData.realizedBasis_central_shift (t : AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType s) (n : ℕ) :
    A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s) ^ n * A.basis t = A.basis (t.shift n) := by
  simp only [D.realizedBasis_eq_sphericalBasis hg hgood hIsogenyQuotient A hA]
  exact AlgebraicGeometry.AbelianScheme.TateComparison.CentralConvolution.sphericalBasis_central_shift s q t n

theorem Data.ActiveHeckeThetaData.activeForms_clearing (u : D.pel.EndQˣ)
    (hu : (u : D.pel.EndQ) = A.algebraAction (A.basis (AlgebraicGeometry.AbelianScheme.TateComparison.Local.LocalType.central s)))
    (w : Intrinsic.Hecke.ActiveWeight) :
    D.heckeRationalForms hg A (A.basis (Intrinsic.Hecke.activeType D.pel.reference.distinguished w)) =
      (D.pel.pullbackForms (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w))).comp
        (D.rationalFormsPullback hg
          ((↑u⁻¹ : D.pel.EndQ) ^ Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished w)) := by
  let : Semigroup D.pel.EndQ := (inferInstance : Ring D.pel.EndQ).toSemigroup
  let t := Intrinsic.Hecke.activeType D.pel.reference.distinguished w
  let n := Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished w
  have hb : (u : D.pel.EndQ) ^ n * A.algebraAction (A.basis t) =
      D.pel.toRational (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)) := by
    rw [hu, ← map_pow, ← map_mul, D.realizedBasis_central_shift hg hgood hIsogenyQuotient A hA]
    exact (hA.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)).symm
  have hc : (↑u⁻¹ : D.pel.EndQ) ^ n * (u : D.pel.EndQ) ^ n = 1 := by
    exact (u ^ n).inv_val
  have he : (↑u⁻¹ : D.pel.EndQ) ^ n *
      D.pel.toRational (A.integral (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished w)) =
      A.algebraAction (A.basis t) := by
    calc
      _ = (↑u⁻¹ : D.pel.EndQ) ^ n *
          ((u : D.pel.EndQ) ^ n * A.algebraAction (A.basis t)) :=
        congrArg (fun z : D.pel.EndQ => (↑u⁻¹ : D.pel.EndQ) ^ n * z) hb.symm
      _ = ((↑u⁻¹ : D.pel.EndQ) ^ n * (u : D.pel.EndQ) ^ n) *
          A.algebraAction (A.basis t) := (mul_assoc _ _ _).symm
      _ = _ := by rw [hc, one_mul]
  change D.rationalFormsPullback hg (A.algebraAction (A.basis t)) = _
  rw [← he, D.rationalFormsPullback_mul, D.rationalFormsPullback_integral]

end

end OAI.RepresentationTheory.Theta.Geometric
