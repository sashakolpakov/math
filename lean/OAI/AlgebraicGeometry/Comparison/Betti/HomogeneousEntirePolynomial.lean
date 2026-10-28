import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorSum
import OAI.AlgebraicGeometry.Comparison.Betti.MultilinearDiagonalPolynomial

/-! # Homogeneous Entire Polynomial -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousEntirePolynomial.Dolbeault

noncomputable section

/-! An entire homogeneous function on a finite complex coordinate space is a homogeneous polynomial. -/

open _root_.TopologicalSpace
open scoped ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def homogeneousFunctionPolynomial (f : (ι → ℂ) → ℂ) (n : ℕ) : MvPolynomial ι ℂ :=
  MvPolynomial.C (n.factorial : ℂ)⁻¹ *
    MultilinearDiagonalPolynomial.Dolbeault.multilinearDiagonalPolynomial n (iteratedFDeriv ℂ n f 0).toMultilinearMap

theorem homogeneousFunctionPolynomial_homogeneous (f : (ι → ℂ) → ℂ) (n : ℕ) :
    (homogeneousFunctionPolynomial f n).IsHomogeneous n :=
  (MultilinearDiagonalPolynomial.Dolbeault.multilinearDiagonalPolynomial_homogeneous n _).C_mul _

theorem homogeneousFunctionPolynomial_eval (f : (ι → ℂ) → ℂ) (hf : ContDiff ℂ ∞ f) (n : ℕ)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x, f (c • x) = c ^ n * f x) (x : ι → ℂ) :
    MvPolynomial.eval x (homogeneousFunctionPolynomial f n) = f x := by
  change MvPolynomial.eval x (MvPolynomial.C (n.factorial : ℂ)⁻¹ *
    MultilinearDiagonalPolynomial.Dolbeault.multilinearDiagonalPolynomial n (iteratedFDeriv ℂ n f 0).toMultilinearMap) = _
  rw [map_mul, MvPolynomial.eval_C, MultilinearDiagonalPolynomial.Dolbeault.multilinearDiagonalPolynomial_eval]
  change (n.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ n f 0 (fun _ => x) = f x
  rw [Laurent.SectorSum.Dolbeault.homogeneousFunction_diagonalDeriv f hf n hscale x, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul]

theorem exists_homogeneousPolynomial_of_entire (a : Holomorphic.FunctionPure.holomorphicFunctions
    (⊤ : Opens (ι → ℂ))) (n : ℕ)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x,
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a (c • x) = c ^ n * Laurent.SectorSum.Dolbeault.laurentEntireFunction a x) :
    ∃ P : MvPolynomial ι ℂ, P.IsHomogeneous n ∧
      ∀ x : ι → ℂ, MvPolynomial.eval x P = Laurent.SectorSum.Dolbeault.laurentEntireFunction a x :=
  ⟨homogeneousFunctionPolynomial (Laurent.SectorSum.Dolbeault.laurentEntireFunction a) n,
    homogeneousFunctionPolynomial_homogeneous _ n,
    homogeneousFunctionPolynomial_eval _ (Laurent.SectorSum.Dolbeault.laurentEntireFunction_contDiff a) n hscale⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousEntirePolynomial.Dolbeault
