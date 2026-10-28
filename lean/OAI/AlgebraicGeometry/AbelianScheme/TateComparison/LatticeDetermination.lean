import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ScaledKernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PolarizedReverse
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GeometricDivision

/-! # Lattice Determination -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! A q-power-bounded Tate lattice is determined by its finite-level
kernel. Applied to polarized isogenies, the bound comes from the actual
polarization reverse map at the good prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct BigOperators

universe u

namespace LatticeDetermination.Tate

variable (q : ℕ) [Fact q.Prime] {H : Type u} [AddCommGroup H]

theorem submodule_eq_of_dividedIntegral_membership (n : ℕ)
    (L M : Submodule ℤ_[q] (Isogeny.Tate.RationalModule q H))
    (hL : ∀ z ∈ L, (q : ℤ_[q]) ^ n • z ∈
      (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.Tate.Module (H := H) q) 1).range)
    (hM : ∀ z ∈ M, (q : ℤ_[q]) ^ n • z ∈
      (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.Tate.Module (H := H) q) 1).range)
    (h : ∀ x : Add.Tate.Module (H := H) q, ScaledKernel.Tate.dividedIntegralVector q n x ∈ L ↔
      ScaledKernel.Tate.dividedIntegralVector q n x ∈ M) : L = M := by
  have hn : (q : ℚ_[q]) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have recover (z : Isogeny.Tate.RationalModule q H) (x : Add.Tate.Module (H := H) q)
      (hx : (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] x = (q : ℤ_[q]) ^ n • z) :
      ScaledKernel.Tate.dividedIntegralVector q n x = z := by
    have hs : (q : ℤ_[q]) ^ n • z = (q : ℚ_[q]) ^ n • z := by
      simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    unfold ScaledKernel.Tate.dividedIntegralVector
    rw [hx, hs]
    exact inv_smul_smul₀ hn z
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx⟩ := hL z hz
    rw [← recover z x hx] at hz ⊢
    exact (h x).mp hz
  · intro z hz
    obtain ⟨x, hx⟩ := hM z hz
    rw [← recover z x hx] at hz ⊢
    exact (h x).mpr hz

end LatticeDetermination.Tate

variable {R : Type u} [CommRing R] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
  {g N m : ℕ} {P Q Q' : PEL.PELFamilyData R g N (Spec (.of k))}
  (q : ℕ) [Fact q.Prime] (e : PELIsogenies.PELIsogeny P Q (q ^ m)) (f : PELIsogenies.PELIsogeny P Q' (q ^ m))
  (δ : Fin g → ℕ) (hδ : P.polarizationMap.HasPolarizationType δ)
  (hq : Nat.Coprime q (∏ i, δ i))

include δ hδ hq in
omit [CharZero k] in
theorem PELIsogenies.PELIsogeny.preimage_eq_of_torsion_kernel_eq
    (h : ∀ z : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m,
      z.val.toMul ≫ e.isogeny.hom = 1 ↔ z.val.toMul ≫ f.isogeny.hom = 1) :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom := by
  apply LatticeDetermination.Tate.submodule_eq_of_dividedIntegral_membership q m
  · intro z hz
    simpa only [Rational.integralTateImage, Nat.cast_pow] using
      e.multiplier_smul_mem_integralTateImage (𝟙 (Spec (.of k))) q δ hδ hq z hz
  · intro z hz
    simpa only [Rational.integralTateImage, Nat.cast_pow] using
      f.multiplier_smul_mem_integralTateImage (𝟙 (Spec (.of k))) q δ hδ hq z hz
  · intro x
    rw [ScaledKernel.dividedIntegralVector_mem_preimage_iff, ScaledKernel.dividedIntegralVector_mem_preimage_iff]
    exact h (x.val m)

theorem PELIsogenies.PELIsogeny.torsion_kernel_eq_of_preimage_eq
    (h : Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
      Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom)
    (z : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m) :
    z.val.toMul ≫ e.isogeny.hom = 1 ↔ z.val.toMul ≫ f.isogeny.hom = 1 := by
  obtain ⟨x, hx⟩ := GeometricDivision.geometricTate_evaluate_surjective P.abelian q m z
  have hx' : (x.val m).val.toMul = z.val.toMul :=
    congrArg (fun w : Add.Tate.torsion q
      (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m => w.val.toMul) hx
  rw [← hx', ← ScaledKernel.dividedIntegralVector_mem_preimage_iff, ← ScaledKernel.dividedIntegralVector_mem_preimage_iff, h]

include δ hδ hq in
theorem PELIsogenies.PELIsogeny.preimage_eq_iff_torsion_kernel_eq :
    Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) e.isogeny.hom =
        Rational.isogenyTatePreimage (T := Over.mk (𝟙 (Spec (.of k)))) (q := q) f.isogeny.hom ↔
      ∀ z : Add.Tate.torsion q (Additive (Over.mk (𝟙 (Spec (.of k))) ⟶ P.abelian.scheme)) m,
        z.val.toMul ≫ e.isogeny.hom = 1 ↔ z.val.toMul ≫ f.isogeny.hom = 1 :=
  ⟨PELIsogenies.PELIsogeny.torsion_kernel_eq_of_preimage_eq q e f, PELIsogenies.PELIsogeny.preimage_eq_of_torsion_kernel_eq q e f δ hδ hq⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
