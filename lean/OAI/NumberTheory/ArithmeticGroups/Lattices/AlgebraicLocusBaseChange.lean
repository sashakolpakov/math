import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.AlgebraicLocus

/-! # Algebraic Locus Base Change -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLocusBaseChange.Construction

noncomputable section

/-! Finiteness of geometric zero sets controls zero sets in every field. -/

open scoped Classical
open _root_.MvPolynomial

theorem zeroLocus_map_scalar_tower
    {k K L σ : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (I : Ideal (MvPolynomial σ k)) :
    zeroLocus L (I.map (MvPolynomial.map (algebraMap k K))) = zeroLocus L I := by
  have he (x : σ → L) (p : MvPolynomial σ k) :
      aeval (R := K) x (MvPolynomial.map (algebraMap k K) p) = aeval (R := k) x p := by
    simp only [aeval_eq_eval₂Hom, eval₂Hom_map_hom, ← IsScalarTower.algebraMap_eq k K L]
  ext x
  change (I.map (MvPolynomial.map (algebraMap k K)) ≤ RingHom.ker (aeval (R := K) x)) ↔
    I ≤ RingHom.ker (aeval (R := k) x)
  rw [Ideal.map_le_iff_le_comap]
  constructor <;> intro h p hp
  · change aeval (R := k) x p = 0
    rw [← he]
    exact h hp
  · change aeval (R := K) x (MvPolynomial.map (algebraMap k K) p) = 0
    rw [he]
    exact h hp

theorem zeroLocus_map_point
    {k K L σ : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (I : Ideal (MvPolynomial σ k)) {x : σ → K} (hx : x ∈ zeroLocus K I) :
    (fun i => algebraMap K L (x i)) ∈ zeroLocus L I := by
  intro p hp
  have he := map_aeval x (algebraMap K L) p
  rw [hx p hp, map_zero, ← IsScalarTower.algebraMap_eq k K L] at he
  exact he.symm

theorem finite_zeroLocus_of_finite_algClosure
    {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : (zeroLocus (AlgebraicClosure k) I).Finite) :
    (zeroLocus K I).Finite := by
  let L := AlgebraicClosure K
  let φ : AlgebraicClosure k →ₐ[k] L := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure k) L := φ.toRingHom.toAlgebra
  let : Module (AlgebraicClosure k) L := Algebra.toModule
  let : IsScalarTower k (AlgebraicClosure k) L :=
    IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  let J := I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
  have hJ : (zeroLocus (AlgebraicClosure k) J).Finite := by
    rw [show J = I.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) from rfl,
      zeroLocus_map_scalar_tower]
    exact hI
  have hL : (zeroLocus L I).Finite := by
    rw [← zeroLocus_map_scalar_tower (K := AlgebraicClosure k)]
    exact Lattices.Finite.AlgebraicLocus.Construction.finite_zeroLocus_field_extension J hJ
  let f : (σ → K) → (σ → L) := fun x i => algebraMap K L (x i)
  have hf : Function.Injective f := by
    intro x y h
    funext i
    exact (algebraMap K L).injective (congrFun h i)
  apply Set.Finite.of_finite_image (f := f) (hL.subset ?_) (hf.injOn)
  rintro _ ⟨x, hx, rfl⟩
  exact zeroLocus_map_point I hx

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicLocusBaseChange.Construction
