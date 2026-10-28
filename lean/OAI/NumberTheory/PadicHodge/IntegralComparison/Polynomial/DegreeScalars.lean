import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeBaseChange

/-! # Degree Scalars -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeScalars.Law

noncomputable section

/-! The scalar normalization of the genuine polynomial-algebra degree
law is the native multiplication degree m^(2g). -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeLaw OAI.NumberTheory.PadicHodge.IntegralComparison.Endomorphism.DegreeIs.Scalar
open OAI.NumberTheory.PadicHodge.IntegralComparison.DegreeNatural.LawScalarExtension

variable {K : Type} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

local instance : IsIntegral A.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.hom

theorem scalar_degreePolynomial :
    Endomorphism.DegreeLaw.degreePolynomial A (fun _ : Fin 1 => (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)) =
      MvPolynomial.X 0 ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  apply MultivariateTailIdentity.eq_of_succ_nat_eval
  intro a
  have hs : (∑ i : Fin 1, (a i + 1) • (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)) = (a 0 + 1) • 1 := by simp
  have hi : (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom.left = 𝟙 A.left := rfl
  have : IsFinite (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom.left := by rw [hi]; infer_instance
  have : IsDominant (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A).toMul.hom.hom.left := by rw [hi]; infer_instance
  have : IsFinite (∑ i : Fin 1, (a i + 1) • (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)).toMul.hom.hom.left := by
    rw [hs]
    exact Endomorphism.DegreeIs.Scalar.nsmul_isFinite A 1 (a 0 + 1) (Nat.succ_pos _)
  have : IsDominant (∑ i : Fin 1, (a i + 1) • (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A)).toMul.hom.hom.left := by
    rw [hs]
    exact Endomorphism.DegreeIs.Scalar.nsmul_isDominant A 1 (a 0 + 1) (Nat.succ_pos _)
  rw [Endomorphism.DegreeLaw.degreePolynomial_eval, map_pow, MvPolynomial.eval_X, hs,
    Endomorphism.DegreeIs.Scalar.nsmul_residueDegree A 1 (a 0 + 1) (Nat.succ_pos _), hi, Scheme.Hom.residueDegree_id,
    mul_one, Nat.cast_pow]

theorem norm_C (L : Type*) [CommRing L] [Algebra ℚ L] (F : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) (c : L) :
    DegreeBaseChange.Law.norm A L F (Polynomial.C c) = c ^ (2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.hom) := by
  rw [DegreeBaseChange.Law.norm_eq_valueBound A L F (Polynomial.C c) 0 (by simp)]
  have hf : (fun i : Fin 1 => F ^ (i : ℕ)) = fun _ => (1 : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A) := by
    funext i
    simp only [Fin.fin_one_eq_zero i, Fin.val_zero, pow_zero]
  unfold DegreeBaseChange.Law.valueBound DegreeNatural.LawScalarExtension.value
  rw [hf, scalar_degreePolynomial]
  simp only [MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, Polynomial.coeff_C,
    Fin.val_zero, ite_true]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.DegreeScalars.Law
