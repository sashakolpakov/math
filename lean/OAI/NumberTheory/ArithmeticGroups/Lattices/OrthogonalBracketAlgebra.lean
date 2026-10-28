import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSymmetricDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.DerivationExponential

/-! # Orthogonal Bracket Algebra -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketAlgebra.Construction

noncomputable section

section

/-! Orthogonal bracket operators are invertible, and their conjugation
preserves symmetric bracket derivations. -/

open _root_.ContinuousLinearMap

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem orthogonalBracketOperators_one (B : L →L[ℝ] L →L[ℝ] L) :
    (1 : L →L[ℝ] L) ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

omit [FiniteDimensional ℝ L] in
theorem orthogonalBracketOperators_mul (B : L →L[ℝ] L →L[ℝ] L)
    {S T : L →L[ℝ] L} (hS : S ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B)
    (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) : S * T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B := by
  constructor
  · intro x y
    change S (T (B x y)) = B (S (T x)) (S (T y))
    rw [hT.1, hS.1]
  · intro x y
    change inner ℝ (S (T x)) (S (T y)) = inner ℝ x y
    rw [hS.2, hT.2]

omit [FiniteDimensional ℝ L] in
theorem orthogonalBracketOperators_injective (B : L →L[ℝ] L →L[ℝ] L)
    {T : L →L[ℝ] L} (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) : Function.Injective T := by
  intro x y h
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← hT.2, map_sub, h, sub_self, inner_zero_left]

def orthogonalBracketEquiv (B : L →L[ℝ] L →L[ℝ] L)
    (T : L →L[ℝ] L) (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) : L ≃L[ℝ] L :=
  (LinearEquiv.ofInjectiveEndo T.toLinearMap (orthogonalBracketOperators_injective B hT)).toContinuousLinearEquiv

theorem orthogonalBracketEquiv_apply (B : L →L[ℝ] L →L[ℝ] L)
    (T : L →L[ℝ] L) (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) (x : L) :
    orthogonalBracketEquiv B T hT x = T x := rfl

theorem orthogonalBracketEquiv_adjoint [CompleteSpace L] (B : L →L[ℝ] L →L[ℝ] L)
    (T : L →L[ℝ] L) (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) :
    adjoint T = (orthogonalBracketEquiv B T hT).symm.toContinuousLinearMap := by
  symm
  apply (eq_adjoint_iff _ _).mpr
  intro x y
  have he := hT.2 ((orthogonalBracketEquiv B T hT).symm x) y
  have hx : T ((orthogonalBracketEquiv B T hT).symm x) = x :=
    (orthogonalBracketEquiv B T hT).apply_symm_apply x
  rw [hx] at he
  exact he.symm

theorem continuousBilinearDerivationDefect_eq_zero_iff
    (B : L →L[ℝ] L →L[ℝ] L) (A : L →L[ℝ] L) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0 ↔
      ∀ x y, A (B x y) = B (A x) y + B x (A y) := by
  constructor
  · intro h x y
    have he := congrArg (fun C : L →L[ℝ] L →L[ℝ] L => C x y) h
    change A (B x y) - B (A x) y - B x (A y) = 0 at he
    exact sub_eq_zero.mp ((sub_sub _ _ _).symm.trans he)
  · intro h
    ext x y
    change A (B x y) - B (A x) y - B x (A y) = 0
    rw [h]
    abel

theorem orthogonalBracketOperators_adjoint [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L) {T : L →L[ℝ] L} (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) :
    adjoint T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B := by
  have hr (x : L) : T (adjoint T x) = x := by
    rw [orthogonalBracketEquiv_adjoint B T hT]
    exact (orthogonalBracketEquiv B T hT).apply_symm_apply x
  constructor
  · intro x y
    apply orthogonalBracketOperators_injective B hT
    rw [hr, hT.1, hr, hr]
  · intro x y
    have he := hT.2 (adjoint T x) (adjoint T y)
    rw [hr, hr] at he
    exact he.symm

theorem orthogonalBracketOperators_adjoint_mul [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L) {T : L →L[ℝ] L} (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B) :
    adjoint T * T = 1 := by
  rw [orthogonalBracketEquiv_adjoint B T hT]
  ext x
  exact (orthogonalBracketEquiv B T hT).symm_apply_apply x

theorem bracket_derivation_conjugate (B : L →L[ℝ] L →L[ℝ] L)
    (g : L ≃L[ℝ] L) (hg : ∀ x y, g (B x y) = B (g x) (g y))
    (A : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (g.conjContinuousAlgEquiv A) = 0 := by
  apply (continuousBilinearDerivationDefect_eq_zero_iff B _).mpr
  intro x y
  obtain ⟨u, rfl⟩ := g.surjective x
  obtain ⟨v, rfl⟩ := g.surjective y
  change g (A (g.symm (B (g u) (g v)))) =
    B (g (A (g.symm (g u)))) (g v) + B (g u) (g (A (g.symm (g v))))
  rw [← hg, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply,
    (continuousBilinearDerivationDefect_eq_zero_iff B A).mp hA, map_add, hg, hg]

theorem orthogonal_conjugate_symmetric_derivation [CompleteSpace L]
    (B : L →L[ℝ] L →L[ℝ] L) (T : L →L[ℝ] L) (hT : T ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B)
    (A : L →L[ℝ] L) (hA : A ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) :
    T * A * adjoint T ∈ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B := by
  constructor
  · intro x y
    change inner ℝ (T (A (adjoint T x))) y = inner ℝ x (T (A (adjoint T y)))
    calc
      _ = inner ℝ (A (adjoint T x)) (adjoint T y) := (adjoint_inner_right T _ _).symm
      _ = inner ℝ (adjoint T x) (A (adjoint T y)) := hA.1 _ _
      _ = _ := adjoint_inner_left T _ _
  · have he : T * A * adjoint T = (orthogonalBracketEquiv B T hT).conjContinuousAlgEquiv A := by
      rw [orthogonalBracketEquiv_adjoint B T hT]
      rfl
    rw [he]
    exact bracket_derivation_conjugate B (orthogonalBracketEquiv B T hT) hT.1 A hA.2

end

/-! Commutators of symmetric derivations are skew-adjoint derivations;
their exponentials are orthogonal bracket automorphisms. -/

open _root_.ContinuousLinearMap NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem bracket_derivation_commutator (B : L →L[ℝ] L →L[ℝ] L)
    (A C : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0)
    (hC : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B C = 0) :
    Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (A * C - C * A) = 0 := by
  have he := DFunLike.congr_fun (ContinuousBracketRepresentation.Construction.continuousBracketRepresentation_commutator A C) B
  change Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (A * C - C * A) =
    ContinuousBracketRepresentation.Construction.continuousBracketRepresentation A (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B C) -
      ContinuousBracketRepresentation.Construction.continuousBracketRepresentation C (Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A) at he
  rw [hA, hC, map_zero, map_zero, sub_self] at he
  exact he

omit [FiniteDimensional ℝ L] in
theorem symmetric_commutator_adjoint [CompleteSpace L] (A C : L →L[ℝ] L)
    (hA : A.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric) :
    adjoint (A * C - C * A) = -(A * C - C * A) := by
  rw [map_sub]
  simp only [mul_def, adjoint_comp, hA.clm_adjoint_eq, hC.clm_adjoint_eq]
  abel

omit [FiniteDimensional ℝ L] in
theorem exp_skew_adjoint_preserves_inner [CompleteSpace L] (A : L →L[ℝ] L)
    (hA : adjoint A = -A) (x y : L) : inner ℝ (exp A x) (exp A y) = inner ℝ x y := by
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hs : A ∈ skewAdjoint (L →L[ℝ] L) := by
    rw [skewAdjoint.mem_iff, star_eq_adjoint, hA]
  have hu := exp_mem_unitary_of_mem_skewAdjoint hs
  have hp : adjoint (exp A) * exp A = (1 : L →L[ℝ] L) :=
    (Unitary.mem_iff.mp hu).1
  have he : adjoint (exp A) (exp A y) = y := DFunLike.congr_fun hp y
  rw [← adjoint_inner_right (exp A), he]

theorem exp_skew_derivation_mem_orthogonal (B : L →L[ℝ] L →L[ℝ] L)
    (A : L →L[ℝ] L) (hA : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B A = 0)
    (hskew : adjoint A = -A) (t : ℝ) : exp (t • A) ∈ OrthogonalBracketCompactness.Construction.orthogonalBracketOperators B := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  have ht : Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (t • A) = 0 := by
    rw [map_smul, hA]
    ext x y
    exact smul_zero t
  refine ⟨Bilinear.DerivationExponential.Construction.exp_bilinear_derivation_preserves B (t • A)
    ((continuousBilinearDerivationDefect_eq_zero_iff B _).mp ht), ?_⟩
  apply exp_skew_adjoint_preserves_inner
  rw [map_smul, hskew, smul_neg]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketAlgebra.Construction
