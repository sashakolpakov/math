import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualCharacteristicPolynomial

/-! # Tate Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TateCharacteristicPolynomial

noncomputable section

/-! Every actual abelian H¹ endomorphism has the characteristic polynomial
of its actual Tate action, integrally and after scalar extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

include hℓ

theorem integral_finite : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := by
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
  let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
  exact Module.Finite.of_injective (Integral.TateNaturality.linearEquiv ℓ A hℓ).toLinearMap
    (Integral.TateNaturality.linearEquiv ℓ A hℓ).injective

theorem integral_free : Module.Free ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := by
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
  let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
  exact Module.Free.of_equiv (Integral.TateNaturality.linearEquiv ℓ A hℓ).symm

theorem integral_charpoly (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
    let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
    let : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_finite ℓ A hℓ
    let : Module.Free ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_free ℓ A hℓ
    (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1).charpoly =
      (Integral.TateNaturality.tateAction ℓ A e).charpoly := by
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
  let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
  let : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_finite ℓ A hℓ
  let : Module.Free ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_free ℓ A hℓ
  let : Module.Finite ℤ_[ℓ] (Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)) :=
    Module.Finite.of_basis (Module.Free.chooseBasis ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)).dualBasis
  let : Module.Free ℤ_[ℓ] (Module.Dual ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)) :=
    Module.Free.of_basis (Module.Free.chooseBasis ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ)).dualBasis
  change (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1).charpoly =
    (Integral.TateNaturality.tateAction ℓ A e).charpoly
  exact (DualCharacteristicPolynomial.of_intertwines (Integral.TateNaturality.linearEquiv ℓ A hℓ)
    (AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1) (Integral.TateNaturality.tateAction ℓ A e).dualMap
    (Integral.TateNaturality.linearEquiv_intertwines ℓ A hℓ e)).trans
      (DualCharacteristicPolynomial.dual (Integral.TateNaturality.tateAction ℓ A e))

theorem scalar_charpoly (B : Type*) [CommRing B] [Algebra ℤ_[ℓ] B] (e : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) :
    let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
    let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
    let : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_finite ℓ A hℓ
    let : Module.Free ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_free ℓ A hℓ
    ((AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1).baseChange B).charpoly =
      ((Integral.TateNaturality.tateAction ℓ A e).baseChange B).charpoly := by
  let : Module.Finite ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.finite A ℓ hℓ
  let : Module.Free ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A) ℓ) := Geometric.TateModule.free A ℓ hℓ
  let : Module.Finite ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_finite ℓ A hℓ
  let : Module.Free ℤ_[ℓ] (A.left.EllAdicCohomology ℓ 1) := integral_free ℓ A hℓ
  change ((AlgebraicGeometry.FormalGeometry.Completion.CohomologyPullback.Construction.integralEllAdicPullbackLinear ℓ e.toMul.hom.hom.left 1).baseChange B).charpoly =
    ((Integral.TateNaturality.tateAction ℓ A e).baseChange B).charpoly
  rw [LinearMap.charpoly_baseChange, LinearMap.charpoly_baseChange, integral_charpoly ℓ A hℓ e]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TateCharacteristicPolynomial
