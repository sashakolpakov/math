import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence

/-! # Torsion Stabilizers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TorsionStabilizers.IntrinsicLinearMaps

noncomputable section

/-! On an actual complex abelian variety, fixing torsion points is
equivalent to principal congruence on its native period lattice. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Maps.IntrinsicAlgebraicMaps OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TorsionCongruence.TorusTorsion

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem quotientLinearMap_eq_torusMap (f : A.toOver ⟶ A.toOver) [IsMonHom f] :
    TorsionCongruence.TorusTorsion.quotientLinearMap (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ)
      (Maps.IntrinsicLinearMaps.linearLift_preserves f) = Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (Maps.IntrinsicLinearMaps.linearLift_lifts f v).symm

omit [NeZero N] in
theorem fixes_native_torsion_iff (f : A.toOver ⟶ A.toOver) [IsMonHom f] :
    (∀ x : TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)) N,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x.val.toMul = x.val.toMul) ↔
    (∀ x : TorsionCongruence.TorusTorsion.killedBy ((Maps.IntrinsicAlgebraicMaps.torus A).Point) N, Maps.IntrinsicAlgebraicMaps.algebraicTorusMap f x.val = x.val) := by
  let e := TorsionCongruence.TorusTorsion.killedByEquiv (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A) N
  constructor
  · intro h x
    have hx := h (e x)
    change (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm
      (Additive.ofMul (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A x.val).toMul)) = x.val
    exact (congrArg (fun y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver =>
      (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm (Additive.ofMul y)) hx).trans
        ((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).symm_apply_apply x.val)
  · intro h x
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy := congrArg (Maps.IntrinsicAlgebraicMaps.periodAddEquiv A) (h y)
    exact congrArg Additive.toMul (((Maps.IntrinsicAlgebraicMaps.periodAddEquiv A).apply_symm_apply _).symm.trans hy)

/-- The stabilizer of native N-torsion is the exact principal
congruence condition on the integral exponential periods. -/
theorem fixes_native_torsion_iff_congruence (f : A.toOver ⟶ A.toOver) [IsMonHom f] :
    (∀ x : TorsionCongruence.TorusTorsion.killedBy (Additive (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints A.toOver)) N,
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x.val.toMul = x.val.toMul) ↔
      ∀ v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, ∃ w ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A,
        Maps.IntrinsicLinearMaps.linearLift f v - v = (N : ℤ) • w := by
  rw [fixes_native_torsion_iff]
  have h := TorsionCongruence.TorusTorsion.fixes_torsion_iff_congruence (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) N
    ((Maps.IntrinsicLinearMaps.linearLift f).restrictScalars ℚ) (Maps.IntrinsicLinearMaps.linearLift_preserves f)
  rw [quotientLinearMap_eq_torusMap] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.TorsionStabilizers.IntrinsicLinearMaps
