import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.TensorProduct
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-! # Spectral -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Spectral.Construction

/-!
# Completion: spectral consequences of the polarization adjoint identity

These are linear-algebra lemmas for the Weil proof, not the geometric
theorem. The adjoint identity must still be derived from a polarization
of the abelian variety. No project statement stub is imported.
-/

open scoped InnerProductSpace

open scoped TensorProduct

/-- The tensor involution is multiplicative in reverse order. -/
noncomputable instance complexTensorStarRing
    {D : Type*} [Ring D] [Algebra ℚ D] [StarRing D] [StarModule ℚ D] :
    StarRing (TensorProduct ℚ ℂ D) where
  star_add := map_add (starLinearEquiv ℚ)
  star_mul x y := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      induction y using TensorProduct.inductionOn with
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.star_tmul, star_mul]
      | add x y hx hy => simp only [mul_add, star_add, add_mul, hx, hy]
    | add x y hx hy => simp only [add_mul, star_add, mul_add, hx, hy]

/-- The complex scalar action is compatible with the tensor involution. -/
instance complexTensorStarModule
    {D : Type*} [Ring D] [Algebra ℚ D] [StarRing D] [StarModule ℚ D] :
    StarModule ℂ (TensorProduct ℚ ℂ D) where
  star_smul c x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp only [TensorProduct.smul_tmul', TensorProduct.star_tmul, star_smul]
    | add x y hx hy => simp only [smul_add, star_add, hx, hy]

/-- A faithful positive functional constructs the inner product used by
the regular representation; no norm or eigenvalue bound is assumed. -/
@[instance_reducible]
def positiveFunctionalCore
    {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    (τ : B →ₗ[ℂ] ℂ)
    (hstar : ∀ x : B, τ (star x) = star (τ x))
    (hpos : ∀ x : B, x ≠ 0 → 0 < (τ (star x * x)).re) :
    InnerProductSpace.Core ℂ B where
  inner x y := τ (star x * y)
  conj_inner_symm x y := by
    change star (τ (star y * x)) = τ (star x * y)
    rw [← hstar, star_mul, star_star]
  re_inner_nonneg x := by
    change 0 ≤ (τ (star x * x)).re
    by_cases hx : x = 0
    · simp [hx]
    · exact (hpos x hx).le
  add_left x y z := by
    simp only [star_add, add_mul, map_add]
  smul_left x y r := by
    change τ (star (r • x) * y) = star r * τ (star x * y)
    rw [star_smul, smul_mul_assoc, map_smul, smul_eq_mul]
  definite x hx := by
    by_contra hne
    have hp := hpos x hne
    change τ (star x * x) = 0 at hx
    rw [hx, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

/-- The involution acts as the adjoint on the inner product just constructed. -/
theorem positiveFunctional_left_adjoint
    {B : Type*} [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]
    [FiniteDimensional ℂ B]
    (τ : B →ₗ[ℂ] ℂ)
    (hstar : ∀ x : B, τ (star x) = star (τ x))
    (hpos : ∀ x : B, x ≠ 0 → 0 < (τ (star x * x)).re) :
    let c := positiveFunctionalCore τ hstar hpos
    letI : NormedAddCommGroup B := c.toNormedAddCommGroup
    letI : InnerProductSpace ℂ B := InnerProductSpace.ofCore c.toCore
    ∀ a : B, (Algebra.lmul ℂ B a).adjoint = Algebra.lmul ℂ B (star a) := by
  let c := positiveFunctionalCore τ hstar hpos
  let : NormedAddCommGroup B := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ B := InnerProductSpace.ofCore c.toCore
  change ∀ a : B, (Algebra.lmul ℂ B a).adjoint = Algebra.lmul ℂ B (star a)
  intro a
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [LinearMap.adjoint_inner_right]
  change τ (star (a * x) * y) = τ (star x * (star a * y))
  rw [star_mul, mul_assoc]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]

/-- The adjoint relation forces the squared norm of an eigenvalue. -/
theorem eigenvalue_norm_sq_of_adjoint_comp
    (T : Module.End ℂ V) (q : ℝ)
    (hT : T.adjoint.comp T = (q : ℂ) • LinearMap.id)
    (z : ℂ) (hz : T.HasEigenvalue z) :
    ‖z‖ ^ 2 = q := by
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hev : T v = z • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hTv : T.adjoint (T v) = (q : ℂ) • v :=
    congrArg (fun S : Module.End ℂ V => S v) hT
  have hi : inner ℂ (T v) (T v) = (q : ℂ) * inner ℂ v v := by
    rw [← LinearMap.adjoint_inner_right, hTv, inner_smul_right]
  have hn : ‖T v‖ ^ 2 = q * ‖v‖ ^ 2 := by
    have hre := congrArg Complex.re hi
    rw [norm_sq_eq_re_inner (𝕜 := ℂ) (T v), norm_sq_eq_re_inner (𝕜 := ℂ) v]
    change (inner ℂ (T v) (T v)).re = q * (inner ℂ v v).re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hre
  rw [hev, norm_smul, mul_pow] at hn
  exact mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)) hn

/-- The positive square root gives the complex absolute value. -/
theorem eigenvalue_norm_of_adjoint_comp
    (T : Module.End ℂ V) (q : ℝ)
    (hT : T.adjoint.comp T = (q : ℂ) • LinearMap.id)
    (z : ℂ) (hz : T.HasEigenvalue z) :
    ‖z‖ = Real.sqrt q := by
  rw [← eigenvalue_norm_sq_of_adjoint_comp T q hT z hz,
    Real.sqrt_sq (norm_nonneg z)]

/-- A common rational characteristic polynomial transfers the adjoint
bound to all complex conjugates of an eigenvalue over any extension of ℚ. -/
theorem algebraic_and_conjugates_of_common_charpoly
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W] [FiniteDimensional L W]
    (F : Module.End L W) (T : Module.End ℂ V)
    (P : Polynomial ℚ)
    (hF : F.charpoly = P.map (algebraMap ℚ L))
    (hTC : T.charpoly = P.map (algebraMap ℚ ℂ))
    (q : ℝ) (hT : T.adjoint.comp T = (q : ℂ) • LinearMap.id)
    (α : L) (hα : F.HasEigenvalue α) :
    IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 →
        ‖z‖ = Real.sqrt q := by
  have hαP : Polynomial.aeval α P = 0 := by
    have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly F α).mp hα
    simpa only [hF, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hroot
  have hP : P ≠ 0 := by
    intro hzero
    have hchar : F.charpoly = 0 := by simpa [hzero] using hF
    exact (LinearMap.charpoly_monic F).ne_zero hchar
  refine ⟨⟨P, hP, hαP⟩, ?_⟩
  intro z hz
  have hzP : Polynomial.aeval z P = 0 := by
    obtain ⟨R, hR⟩ := minpoly.dvd ℚ α hαP
    rw [hR, map_mul, hz, zero_mul]
  apply eigenvalue_norm_of_adjoint_comp T q hT z
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr
  simpa only [hTC, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hzP

/-- An eigenvalue is a root of every polynomial annihilating its operator. -/
theorem eigenvalue_isRoot_of_annihilating_polynomial
    {L : Type*} [Field L]
    {W : Type*} [AddCommGroup W] [Module L W]
    (F : Module.End L W) (P : Polynomial L)
    (hP : Polynomial.aeval F P = 0)
    (α : L) (hα : F.HasEigenvalue α) : P.IsRoot α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have h := Module.End.aeval_apply_of_hasEigenvector (p := P) hv
  rw [hP, LinearMap.zero_apply] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hv.2

/-- The faithful complex representation and the ℓ-adic representation
may have different dimensions: annihilation suffices for the latter. -/
theorem algebraic_and_conjugates_of_annihilator
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W]
    (F : Module.End L W) (T : Module.End ℂ V)
    (P : Polynomial ℚ)
    (hF : Polynomial.aeval F (P.map (algebraMap ℚ L)) = 0)
    (hTC : T.charpoly = P.map (algebraMap ℚ ℂ))
    (q : ℝ) (hT : T.adjoint.comp T = (q : ℂ) • LinearMap.id)
    (α : L) (hα : F.HasEigenvalue α) :
    IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 →
        ‖z‖ = Real.sqrt q := by
  have hαP : Polynomial.aeval α P = 0 := by
    have hroot := eigenvalue_isRoot_of_annihilating_polynomial
      F (P.map (algebraMap ℚ L)) hF α hα
    simpa only [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hroot
  have hP : P ≠ 0 := by
    intro hzero
    have hchar : T.charpoly = 0 := by simpa [hzero] using hTC
    exact (LinearMap.charpoly_monic T).ne_zero hchar
  refine ⟨⟨P, hP, hαP⟩, ?_⟩
  intro z hz
  have hzP : Polynomial.aeval z P = 0 := by
    obtain ⟨R, hR⟩ := minpoly.dvd ℚ α hαP
    rw [hR, map_mul, hz, zero_mul]
  apply eigenvalue_norm_of_adjoint_comp T q hT z
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly T z).mpr
  simpa only [hTC, Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hzP

/-- The regular representation supplies an annihilating rational polynomial
for every representation of a finite-dimensional rational algebra. -/
theorem algebraic_and_conjugates_of_regular_adjoint
    {D : Type*} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W]
    [Algebra ℚ (Module.End L W)] [IsScalarTower ℚ L (Module.End L W)]
    (e : TensorProduct ℚ ℂ D ≃ₗ[ℂ] V)
    (ρ : D →ₐ[ℚ] Module.End L W)
    (π : D) (q : ℝ)
    (hT : (e.conj ((Algebra.lmul ℚ D π).baseChange ℂ)).adjoint.comp
        (e.conj ((Algebra.lmul ℚ D π).baseChange ℂ)) =
          (q : ℂ) • LinearMap.id)
    (α : L) (hα : (ρ π).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 →
        ‖z‖ = Real.sqrt q := by
  apply algebraic_and_conjugates_of_annihilator (ρ π)
    (e.conj ((Algebra.lmul ℚ D π).baseChange ℂ)) (Algebra.lmul ℚ D π).charpoly
    ?_ ?_ q hT α hα
  · rw [Polynomial.aeval_map_algebraMap]
    rw [Polynomial.aeval_algHom_apply, Algebra.aeval_self_charpoly_lmul, map_zero]
  · rw [LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange]

/-- The complex regular representation transported to an inner-product space. -/
noncomputable def complexRegularRepresentation
    {D : Type*} [Ring D] [Algebra ℚ D]
    (e : TensorProduct ℚ ℂ D ≃ₗ[ℂ] V) :
    D →+* Module.End ℂ V :=
  e.conjRingEquiv.toRingHom.comp
    ((Module.End.baseChangeHom ℚ ℂ D).toRingHom.comp
      (Algebra.lmul ℚ D).toRingHom)

/-- Algebraic core of the Weil argument: an involution represented by the
positive inner-product adjoint and the relation π†π = q imply the bound
in every representation over an extension of ℚ. The geometric Rosati
positivity theorem is needed to supply these data for an abelian variety. -/
theorem algebraic_and_conjugates_of_involution
    {D : Type*} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] [StarRing D]
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W]
    [Algebra ℚ (Module.End L W)] [IsScalarTower ℚ L (Module.End L W)]
    (e : TensorProduct ℚ ℂ D ≃ₗ[ℂ] V)
    (hAdj : ∀ a : D, (complexRegularRepresentation e a).adjoint =
      complexRegularRepresentation e (star a))
    (ρ : D →ₐ[ℚ] Module.End L W)
    (π : D) (q : ℕ) (hπ : star π * π = (q : D))
    (α : L) (hα : (ρ π).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 →
        ‖z‖ = Real.sqrt (q : ℝ) := by
  apply algebraic_and_conjugates_of_regular_adjoint e ρ π (q : ℝ) ?_ α hα
  change (complexRegularRepresentation e π).adjoint *
      complexRegularRepresentation e π = ((q : ℝ) : ℂ) • LinearMap.id
  rw [hAdj, ← map_mul, hπ, map_natCast]
  ext v
  simp [Nat.cast_smul_eq_nsmul]

/-- Complete algebraic reduction from a faithful positive functional on
the complexified rational algebra. In the geometric proof the functional
and its positivity must be constructed from a polarization. -/
theorem algebraic_and_conjugates_of_positive_functional
    {D : Type*} [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    [StarRing D] [StarModule ℚ D]
    (τ : TensorProduct ℚ ℂ D →ₗ[ℂ] ℂ)
    (hstar : ∀ x : TensorProduct ℚ ℂ D, τ (star x) = star (τ x))
    (hpos : ∀ x : TensorProduct ℚ ℂ D, x ≠ 0 → 0 < (τ (star x * x)).re)
    {L : Type*} [Field L] [Algebra ℚ L]
    {W : Type*} [AddCommGroup W] [Module L W]
    [Algebra ℚ (Module.End L W)] [IsScalarTower ℚ L (Module.End L W)]
    (ρ : D →ₐ[ℚ] Module.End L W)
    (π : D) (q : ℕ) (hπ : star π * π = (q : D))
    (α : L) (hα : (ρ π).HasEigenvalue α) :
    IsAlgebraic ℚ α ∧
      ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ α) = 0 →
        ‖z‖ = Real.sqrt (q : ℝ) := by
  let c := positiveFunctionalCore τ hstar hpos
  let : NormedAddCommGroup (TensorProduct ℚ ℂ D) := c.toNormedAddCommGroup
  let : InnerProductSpace ℂ (TensorProduct ℚ ℂ D) := InnerProductSpace.ofCore c.toCore
  apply algebraic_and_conjugates_of_involution
    (LinearEquiv.refl ℂ (TensorProduct ℚ ℂ D)) ?_ ρ π q hπ α hα
  intro a
  change ((Algebra.lmul ℚ D a).baseChange ℂ).adjoint =
    (Algebra.lmul ℚ D (star a)).baseChange ℂ
  rw [Algebra.baseChange_lmul, Algebra.baseChange_lmul]
  have ha := positiveFunctional_left_adjoint τ hstar hpos (1 ⊗ₜ[ℚ] a)
  simpa only [TensorProduct.star_tmul, star_one] using ha

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Spectral.Construction
