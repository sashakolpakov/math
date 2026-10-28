import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateEquivalence
import OAI.NumberTheory.PadicHodge.IntegralComparison.AdditiveLinearity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.EndomorphismNaturality

/-! # Tate Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality

noncomputable section

/-! The actual integral H¹–Tate comparison is linear and carries every
algebraic endomorphism pullback to the dual of its actual Tate action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TatePairing

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

theorem pairing_smul (a : ℤ_[ℓ]) (x : A.left.EllAdicCohomology ℓ 1) :
    TatePairing.pairing ℓ A hℓ (a • x) = a • TatePairing.pairing ℓ A hℓ x := by
  apply LinearMap.ext
  intro t
  let f : A.left.EllAdicCohomology ℓ 1 →+ ℤ_[ℓ] := {
    toFun y := TatePairing.pairing ℓ A hℓ y t
    map_zero' := by rw [map_zero]; rfl
    map_add' y z := by rw [map_add]; rfl }
  exact AdditiveLinearity.map_smul ℓ f a x

def linearEquiv : A.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
    Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) :=
  { TateEquivalence.equiv ℓ A hℓ with map_smul' := pairing_smul ℓ A hℓ }

@[simp] theorem linearEquiv_apply (x : A.left.EllAdicCohomology ℓ 1) :
    linearEquiv ℓ A hℓ x = TatePairing.pairing ℓ A hℓ x := rfl

def tateAction (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) : Module.End ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) :=
  AlgebraicGeometry.AbelianScheme.TateComparison.Add.schemeTateMap A (𝟙_ (Over (Spec (.of k)))) ℓ e.toMul.hom.hom

theorem pairing_pullback (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (x : A.left.EllAdicCohomology ℓ 1)
    (t : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) :
    TatePairing.pairing ℓ A hℓ (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.integralEllAdicPullback ℓ e.toMul.hom.hom.left 1 x) t =
      TatePairing.pairing ℓ A hℓ x (tateAction ℓ A e t) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [TatePairing.pairing_reduction, TatePairing.pairing_reduction, ← AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientPullback.Construction.integralEllAdicFiniteReduction_pullback]
  exact Finite.EndomorphismNaturality.pairing ℓ n A hℓ e
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 x) (TatePairing.torsionEquiv ℓ A n (t.val n)).toMul

theorem linearEquiv_pullback (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (x : A.left.EllAdicCohomology ℓ 1) :
    linearEquiv ℓ A hℓ (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1 x) =
      (tateAction ℓ A e).dualMap (linearEquiv ℓ A hℓ x) := by
  apply LinearMap.ext
  intro t
  exact pairing_pullback ℓ A hℓ e x t

theorem linearEquiv_intertwines (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    (linearEquiv ℓ A hℓ).toLinearMap.comp
      (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1) =
    (tateAction ℓ A e).dualMap.comp (linearEquiv ℓ A hℓ).toLinearMap := by
  apply LinearMap.ext
  exact linearEquiv_pullback ℓ A hℓ e

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality
