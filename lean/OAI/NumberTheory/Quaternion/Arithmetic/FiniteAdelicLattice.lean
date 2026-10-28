import OAI.NumberTheory.Quaternion.Arithmetic.ScalarApproximation

/-! # Finite Adelic Lattice -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicLattice

noncomputable section

section

/-! Integral rational finite adeles are algebraic integers. A common
nonzero algebraic integer clears a finite family of adelic denominators. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F]

theorem scalarFiniteAdele_integral_iff (x : F) :
    algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) x ∈ ScalarApproximation.integralScalarAdeles F ↔
      x ∈ (algebraMap (𝓞 F) F).range := by
  constructor
  · intro hx
    apply mem_integers_of_valuation_le_one F x
    intro v
    have hv := hx v
    change Valued.v (x : v.adicCompletion F) ≤ 1 at hv
    rwa [adicCompletion.valued_coe] at hv
  · rintro ⟨a, rfl⟩
    intro v
    exact coe_mem_adicCompletionIntegers (K := F) v a

theorem integralScalarAdeles_scalar_mul (d : 𝓞 F) {a : ScalarApproximation.ScalarFiniteAdeles F}
    (ha : a ∈ ScalarApproximation.integralScalarAdeles F) :
    algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * a ∈ ScalarApproximation.integralScalarAdeles F :=
  (ScalarApproximation.integralScalarAdeles F).mul_mem (ScalarApproximation.algebraMap_mem_integralScalarAdeles F d) ha

theorem exists_integralScalar_family_multiple {ι : Type*} [Fintype ι]
    (a : ι → ScalarApproximation.ScalarFiniteAdeles F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ i,
      algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * a i ∈ ScalarApproximation.integralScalarAdeles F := by
  choose d hd hda using fun i => ScalarApproximation.exists_integralScalar_multiple F (a i)
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.mpr (fun i _ => hd i), ?_⟩
  intro i
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  rw [hk, map_mul]
  have h := integralScalarAdeles_scalar_mul k (hda i)
  convert h using 1
  ring

end

section

/-! Pulling integral finite-adelic vectors back along an adelic matrix
defines an integral module in the rational vector space. Common
denominators give a full coordinate lattice inside this module. -/

open scoped Classical _root_.NumberField _root_.Matrix

variable {F : Type} [Field F] [NumberField F] (n : ℕ)

def integralFiniteAdelicVectors : Submodule (𝓞 F) (Fin n → ScalarApproximation.ScalarFiniteAdeles F) where
  carrier := {x | ∀ i, x i ∈ ScalarApproximation.integralScalarAdeles F}
  zero_mem' _ := (ScalarApproximation.integralScalarAdeles F).zero_mem
  add_mem' hx hy i := (ScalarApproximation.integralScalarAdeles F).add_mem (hx i) (hy i)
  smul_mem' d _ hx i := integralScalarAdeles_scalar_mul d (hx i)

def rationalFiniteAdelicVectorMap : (Fin n → F) →ₗ[𝓞 F] (Fin n → ScalarApproximation.ScalarFiniteAdeles F) where
  toFun x i := algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (x i)
  map_add' x y := by
    funext i
    exact map_add (algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)) (x i) (y i)
  map_smul' d x := by
    funext i
    change algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) ((algebraMap (𝓞 F) F d) * x i) =
      algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (x i)
    rw [map_mul, ← IsScalarTower.algebraMap_apply]

variable {n}

def finiteAdelicMatrixLattice (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) :
    Submodule (𝓞 F) (Fin n → F) :=
  (integralFiniteAdelicVectors n).comap
    ((A.mulVecLin.restrictScalars (𝓞 F)).comp (rationalFiniteAdelicVectorMap n))

theorem mem_finiteAdelicMatrixLattice
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) (x : Fin n → F) :
    x ∈ finiteAdelicMatrixLattice A ↔ ∀ i,
      (A *ᵥ fun j => algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (x j)) i ∈ ScalarApproximation.integralScalarAdeles F := Iff.rfl

theorem mem_finiteAdelicMatrixLattice_one (x : Fin n → F) :
    x ∈ finiteAdelicMatrixLattice (1 : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) ↔
      ∀ i, x i ∈ (algebraMap (𝓞 F) F).range := by
  rw [mem_finiteAdelicMatrixLattice, Matrix.one_mulVec]
  exact forall_congr' fun i => scalarFiniteAdele_integral_iff (x i)

theorem integralFiniteAdelicVectors_mulVec
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F))
    (hA : ∀ i j, A i j ∈ ScalarApproximation.integralScalarAdeles F)
    (x : Fin n → ScalarApproximation.ScalarFiniteAdeles F) (hx : x ∈ integralFiniteAdelicVectors n) :
    A *ᵥ x ∈ integralFiniteAdelicVectors n := by
  intro i
  exact (ScalarApproximation.integralScalarAdeles F).sum_mem fun j _ =>
    (ScalarApproximation.integralScalarAdeles F).mul_mem (hA i j) (hx j)

theorem finiteAdelicMatrixLattice_contains_coordinate_multiple
    (A : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x : Fin n → F,
      (∀ i, x i ∈ (algebraMap (𝓞 F) F).range) → d • x ∈ finiteAdelicMatrixLattice A := by
  obtain ⟨d, hd, hA⟩ := exists_integralScalar_family_multiple (fun ij : Fin n × Fin n => A ij.1 ij.2)
  refine ⟨d, hd, ?_⟩
  intro x hx
  rw [mem_finiteAdelicMatrixLattice]
  intro i
  change (∑ j, A i j * algebraMap F (ScalarApproximation.ScalarFiniteAdeles F)
    (algebraMap (𝓞 F) F d * x j)) ∈ ScalarApproximation.integralScalarAdeles F
  apply (ScalarApproximation.integralScalarAdeles F).sum_mem
  intro j _
  have he : A i j * algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (algebraMap (𝓞 F) F d * x j) =
      (algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * A i j) *
        algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (x j) := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    ring
  rw [he]
  exact (ScalarApproximation.integralScalarAdeles F).mul_mem (hA (i, j)) ((scalarFiniteAdele_integral_iff (x j)).mpr (hx j))

end

/-! An invertible adelic matrix gives an integral module with bounded
denominators in both directions. -/

open scoped Classical _root_.NumberField _root_.Matrix

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem finiteAdelicMatrixLattice_clear_denominators
    (A B : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) (hBA : B * A = 1) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ x ∈ finiteAdelicMatrixLattice A,
      d • x ∈ finiteAdelicMatrixLattice (1 : Matrix (Fin n) (Fin n) (ScalarApproximation.ScalarFiniteAdeles F)) := by
  obtain ⟨d, hd, hB⟩ := exists_integralScalar_family_multiple (fun ij : Fin n × Fin n => B ij.1 ij.2)
  refine ⟨d, hd, ?_⟩
  intro x hx
  rw [mem_finiteAdelicMatrixLattice_one]
  intro i
  apply (scalarFiniteAdele_integral_iff ((d • x) i)).mp
  let v := rationalFiniteAdelicVectorMap n x
  have hv : B *ᵥ (A *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have hvi : algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (x i) = (B *ᵥ (A *ᵥ v)) i :=
    congrFun hv.symm i
  change algebraMap F (ScalarApproximation.ScalarFiniteAdeles F) (algebraMap (𝓞 F) F d * x i) ∈ ScalarApproximation.integralScalarAdeles F
  rw [map_mul, ← IsScalarTower.algebraMap_apply, hvi]
  change algebraMap (𝓞 F) (ScalarApproximation.ScalarFiniteAdeles F) d * (∑ j, B i j * (A *ᵥ v) j) ∈ ScalarApproximation.integralScalarAdeles F
  rw [Finset.mul_sum]
  apply (ScalarApproximation.integralScalarAdeles F).sum_mem
  intro j _
  rw [← mul_assoc]
  exact (ScalarApproximation.integralScalarAdeles F).mul_mem (hB (i, j)) (hx j)

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicLattice
