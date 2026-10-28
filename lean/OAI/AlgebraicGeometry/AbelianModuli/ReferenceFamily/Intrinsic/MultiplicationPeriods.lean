import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps

/-! # Multiplication Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps

noncomputable section

/-! Natural multiplication in the actual group scheme acts by the
same natural scalar on its native complex and rational periods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f]

instance nativePow_isMonHom (n : ℕ) : IsMonHom (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; infer_instance
  | succ n ih =>
      let : IsMonHom (f ^ n) := ih
      rw [pow_succ]
      exact Maps.IntrinsicLinearMaps.nativeMul_isMonHom (f ^ n) f

theorem linearLift_pow (n : ℕ) : Maps.IntrinsicLinearMaps.linearLift (f ^ n) = n • Maps.IntrinsicLinearMaps.linearLift f := by
  induction n with
  | zero =>
      exact (Maps.IntrinsicLinearMaps.linearLift_congr _ _ (pow_zero f)).trans
        ((Maps.IntrinsicLinearMaps.linearLift_zero A B).trans (zero_smul ℕ (Maps.IntrinsicLinearMaps.linearLift f)).symm)
  | succ n ih =>
      calc
        Maps.IntrinsicLinearMaps.linearLift (f ^ (n + 1)) = Maps.IntrinsicLinearMaps.linearLift (f ^ n * f) := Maps.IntrinsicLinearMaps.linearLift_congr _ _ (pow_succ f n)
        _ = Maps.IntrinsicLinearMaps.linearLift (f ^ n) + Maps.IntrinsicLinearMaps.linearLift f := Maps.IntrinsicLinearMaps.linearLift_add _ _
        _ = (n + 1) • Maps.IntrinsicLinearMaps.linearLift f := by rw [ih, succ_nsmul]

theorem rationalLift_pow (n : ℕ) : IntegralMaps.IntrinsicLinearMaps.rationalLift (f ^ n) = n • IntegralMaps.IntrinsicLinearMaps.rationalLift f := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (linearLift_pow f n) v.val

theorem rationalLift_multiplication (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    IntegralMaps.IntrinsicLinearMaps.rationalLift ((𝟙 A.toOver) ^ n) = n • LinearMap.id :=
  (rationalLift_pow (𝟙 A.toOver) n).trans (congrArg (fun L => n • L) (IntegralMaps.IntrinsicLinearMaps.rationalLift_id A))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.MultiplicationPeriods.IntrinsicLinearMaps
