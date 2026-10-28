import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.TruncatedModel
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Nilpotence -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original special-fiber immersion has a globally nilpotent
ideal sheaf. Maps into an unramified target are uniquely determined
by their restriction to that original special fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.truncatedReduction_ker_pow (n : ℕ) : (A.truncatedReduction n).ker ^ (n + 1) = 0 := by
  apply Scheme.IdealSheafData.ext
  funext U
  change ((A.truncatedReduction n).ker.ideal U) ^ (n + 1) = ⊥
  calc
    _ = (Ideal.span {(q : Γ((A.truncatedModel n).scheme.left, U))}) ^ (n + 1) :=
      congrArg (fun I : Ideal Γ((A.truncatedModel n).scheme.left, U) => I ^ (n + 1))
        (((A.truncatedReduction n).ker_apply U).trans (A.truncatedReduction_kernel n U U.2))
    _ = Ideal.span {(q : Γ((A.truncatedModel n).scheme.left, U)) ^ (n + 1)} :=
      Ideal.span_singleton_pow _ _
    _ = ⊥ := Ideal.span_singleton_eq_bot.mpr (A.truncated_prime_power_zero n U)

theorem Geometry.AbelianH1Model.truncatedReduction_ker_nilpotent (n : ℕ) : IsNilpotent (A.truncatedReduction n).ker :=
  ⟨n + 1, A.truncatedReduction_ker_pow n⟩

theorem Geometry.AbelianH1Model.truncatedReduction_hom_ext (n : ℕ) {Y S : Scheme} (f : Y ⟶ S)
    [FormallyUnramified f] {g₁ g₂ : (A.truncatedModel n).scheme.left ⟶ Y}
    (hred : A.truncatedReduction n ≫ g₁ = A.truncatedReduction n ≫ g₂)
    (hbase : g₁ ≫ f = g₂ ≫ f) : g₁ = g₂ :=
  FormallyUnramified.hom_ext (A.truncatedReduction n)
    (A.truncatedReduction_ker_nilpotent n) f hred hbase

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
