import OAI.NumberTheory.ArithmeticGroups.Lattices.SmoothDerivationExtension
import OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroFieldSmooth

/-! # Differential Constants -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialConstants.Construction

noncomputable section

/-! In a characteristic-zero field extension, an element killed by all
base-field derivations is algebraic over the base. Over an algebraically
closed base it is a constant. -/

open scoped Classical

theorem transcendental_exists_derivation_eq_one
    {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
    {x : K} (hx : Transcendental k x) : ∃ D : Derivation k K K, D x = 1 := by
  let f : Polynomial k →ₐ[k] K := Polynomial.aeval x
  let : Algebra (Polynomial k) K := f.toRingHom.toAlgebra
  let : IsScalarTower k (Polynomial k) K :=
    IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  let : FaithfulSMul (Polynomial k) K :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial k) K).mpr
      (transcendental_iff_injective.mp hx)
  let : Algebra (FractionRing (Polynomial k)) K := FractionRing.liftAlgebra (Polynomial k) K
  let : IsScalarTower (Polynomial k) (FractionRing (Polynomial k)) K :=
    FractionRing.isScalarTower_liftAlgebra (Polynomial k) K
  let : Algebra.FormallySmooth (Polynomial k) (FractionRing (Polynomial k)) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors (Polynomial k))
  let : Algebra.FormallySmooth (FractionRing (Polynomial k)) K :=
    CharZeroFieldSmooth.Construction.charZero_field_extension_formallySmooth _ _
  let : Algebra.FormallySmooth (Polynomial k) K :=
    Algebra.FormallySmooth.comp (Polynomial k) (FractionRing (Polynomial k)) K
  obtain ⟨D, hD⟩ := SmoothDerivationExtension.Construction.exists_derivation_extension_of_formallySmooth (Polynomial.mkDerivation k (1 : K))
  refine ⟨D, ?_⟩
  have he : algebraMap (Polynomial k) K Polynomial.X = x := Polynomial.aeval_X x
  have hh := hD Polynomial.X
  rwa [he, Polynomial.mkDerivation_X] at hh

theorem algebraic_of_all_derivations_zero
    {k K : Type*} [Field k] [CharZero k] [Field K] [Algebra k K]
    (x : K) (hx : ∀ D : Derivation k K K, D x = 0) : IsAlgebraic k x := by
  by_contra h
  obtain ⟨D, hD⟩ := transcendental_exists_derivation_eq_one h
  exact one_ne_zero (hD.symm.trans (hx D))

theorem constant_of_all_derivations_zero
    {k K : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Field K] [Algebra k K]
    (x : K) (hx : ∀ D : Derivation k K K, D x = 0) :
    ∃ c : k, algebraMap k K c = x := by
  have h := algebraic_of_all_derivations_zero x hx
  let L := IntermediateField.adjoin k {x}
  let : FiniteDimensional k L := IntermediateField.adjoin.finiteDimensional h.isIntegral
  let y : L := ⟨x, IntermediateField.subset_adjoin k {x} (Set.mem_singleton x)⟩
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := L)).surjective y
  exact ⟨c, congrArg (fun z : L => z.val) hc⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialConstants.Construction
