import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusFactorShiftEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry

/-! # Frobenius Etale -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.FrobeniusEtale

noncomputable section

/-! Polynomial evaluations of the original geometric Frobenius are
finite étale whenever their constant coefficient is prime to the base
characteristic. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.Obj

open OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeGeometry.Law

variable (k : Type) [Field k] [Fintype k]
  (A : Over (Spec (CommRingCat.of k))) [GrpObj A] [IsCommMonObj A]

omit [Fintype k] in
theorem naturalEnd_split (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ) :
    DegreeGeometry.Law.naturalEnd A F R = (R.coeff 0 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) + DegreeGeometry.Law.naturalEnd A F R.divX * F := by
  unfold DegreeGeometry.Law.naturalEnd
  calc
    _ = Polynomial.eval₂ (Nat.castRingHom (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)) F
        (Polynomial.X * R.divX + Polynomial.C (R.coeff 0)) :=
      congrArg _ (Polynomial.X_mul_divX_add R).symm
    _ = _ := by
      rw [Polynomial.eval₂_add, Polynomial.eval₂_X_mul, Polynomial.eval₂_C]
      exact add_comm _ _

omit [Fintype k] in
theorem naturalEnd_add_C (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ) (n : ℕ) :
    DegreeGeometry.Law.naturalEnd A F (R + Polynomial.C n) = DegreeGeometry.Law.naturalEnd A F R + (n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) := by
  simp only [DegreeGeometry.Law.naturalEnd, Polynomial.eval₂_add, Polynomial.eval₂_C]
  rfl

omit [Fintype k] in
theorem naturalEnd_baseChange (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (R : Polynomial ℕ) :
    AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (DegreeGeometry.Law.naturalEnd A F R) =
      DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A) (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A F) R := by
  unfold DegreeGeometry.Law.naturalEnd
  rw [Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

theorem polynomial_shift_eq (R : Polynomial ℕ) (n : ℕ) :
    DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)) (R + Polynomial.C n) =
    ((R.coeff 0 + n : ℕ) : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)) -
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A
        ((-DegreeGeometry.Law.naturalEnd A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) R.divX) * AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) := by
  rw [← naturalEnd_baseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) (R + Polynomial.C n),
    naturalEnd_add_C k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) R n,
    naturalEnd_split k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) R]
  simp only [map_add, map_natCast, map_mul, map_neg, Nat.cast_add, neg_mul, sub_neg_eq_add]
  abel

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

theorem shifted_finite_etale (R : Polynomial ℕ) (n : ℕ) (hn : ((R.coeff 0 + n : ℕ) : k) ≠ 0) :
    IsFinite (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A))
        (R + Polynomial.C n)).toMul.hom.hom.left ∧
    Surjective (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A))
        (R + Polynomial.C n)).toMul.hom.hom.left ∧
    Etale (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A))
        (R + Polynomial.C n)).toMul.hom.hom.left := by
  rw [polynomial_shift_eq]
  exact Geometric.FrobeniusFactorShiftEtale.finite_etale k A
    (-DegreeGeometry.Law.naturalEnd A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A) R.divX) (R.coeff 0 + n) hn

theorem finite_etale (R : Polynomial ℕ) (hR : (R.coeff 0 : k) ≠ 0) :
    IsFinite (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)) R).toMul.hom.hom.left ∧
    Surjective (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)) R).toMul.hom.hom.left ∧
    Etale (DegreeGeometry.Law.naturalEnd (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver k A)
        (AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange k A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius k A)) R).toMul.hom.hom.left := by
  simpa only [Nat.add_zero, Polynomial.C_0, add_zero] using
    shifted_finite_etale k A R 0 (by simpa only [Nat.add_zero] using hR)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.FrobeniusEtale
