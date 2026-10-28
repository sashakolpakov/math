import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TateDegree
import OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs

/-! # Tate Rank -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateRank

noncomputable section

/-! The rank of the native geometric Tate module is twice the dimension,
by the actual degree of multiplication and the finite-kernel determinant. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.KernelDegree

variable {k : Type} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)

omit [IsAlgClosed k] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem pointAction_power (n : ℕ) :
    FiniteEtale.KernelDegree.pointAction A ((𝟙 A : A ⟶ A) ^ n) = n • AddMonoidHom.id (TateModule.Points A) := by
  apply AddMonoidHom.ext
  intro x
  apply Additive.toMul.injective
  change x.toMul ≫ ((𝟙 A : A ⟶ A) ^ n) = x.toMul ^ n
  rw [MonObj.comp_pow, Category.comp_id]

include hp

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem finrank :
    Module.finrank ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points A) p) =
      2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom := by
  let : Module.Finite ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points A) p) := TateModule.finite A p hp
  let : Module.Free ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points A) p) := TateModule.free A p hp
  let f := ((𝟙 A : A ⟶ A) ^ p)
  let : IsFinite f.left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_isFinite A p hp
  let : Etale f.left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_etale A p hp
  let : Surjective f.left := AlgebraicGeometry.FormalGeometry.Completion.Multiplication.Construction.multiplication_surjective A p hp
  have he := FiniteEtale.TateDegree.determinant_valuation A p hp f
  rw [Endomorphism.DegreeIs.Divisibility.multiplication_residueDegree_eq_power_dimension
    A p (Fact.out : p.Prime).pos, Nat.factorization_pow_self (Fact.out : p.Prime)] at he
  rw [pointAction_power A p, AlgebraicGeometry.AbelianScheme.TateComparison.Functor.Tate.map_nsmul, AlgebraicGeometry.AbelianScheme.TateComparison.Functor.Tate.map_id,
    ← Nat.cast_smul_eq_nsmul ℤ_[p], LinearMap.det_smul, LinearMap.det_id,
    mul_one, PadicInt.valuation_pow, PadicInt.valuation_p, mul_one] at he
  exact he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateRank
