import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.StratumNeighborhood
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nilpotent.Basic

/-! # Supported Affine Center Extension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.SupportedAffineCenterExtension.Construction

noncomputable section

/-! Extending a center from a principal open when its support stays
inside a closed stratum wholly contained in that open. -/

variable {R : Type*} [CommRing R]

/-- A center on `D(f)` supported on a power of `F`, with `f = 1` modulo
`F`, extends by contraction to an ideal on the whole affine ring. In the
extended center's quotient, `f` is already invertible. -/
theorem supported_affine_center_parameter_unit
    (F : Ideal R) (f : R) (hf : 1 - f ∈ F)
    (C : Ideal (Localization.Away f)) (N : ℕ)
    (hC : (F ^ N).map (algebraMap R (Localization.Away f)) ≤ C) :
    IsUnit (Ideal.Quotient.mk (C.comap (algebraMap R (Localization.Away f))) f) := by
  let I := C.comap (algebraMap R (Localization.Away f))
  have hpow : (1 - f) ^ N ∈ I := hC (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hf N))
  have hnil : IsNilpotent (Ideal.Quotient.mk I (1 - f)) := by
    refine ⟨N, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hpow
  simpa only [map_sub, map_one, sub_sub_cancel] using hnil.isUnit_one_sub

/-- Once `f` is a unit on the contracted center, its quotient is exactly
the original center quotient on `D(f)`. This is the actual canonical map. -/
theorem supported_affine_center_quotientMap_bijective
    (f : R) (C : Ideal (Localization.Away f))
    (hu : IsUnit (Ideal.Quotient.mk (C.comap (algebraMap R (Localization.Away f))) f)) :
    Function.Bijective (Ideal.quotientMap C (algebraMap R (Localization.Away f)) le_rfl) := by
  let I := C.comap (algebraMap R (Localization.Away f))
  let φ := Ideal.quotientMap C (algebraMap R (Localization.Away f)) le_rfl
  let qR := Ideal.Quotient.mk I
  let qL := Ideal.Quotient.mk C
  refine ⟨Ideal.quotientMap_injective, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  let r := (IsLocalization.Away.sec f x).1
  let n := (IsLocalization.Away.sec f x).2
  obtain ⟨u, hu⟩ := hu
  have hden : qL (algebraMap R (Localization.Away f) (f ^ n)) = φ ((u : R ⧸ I) ^ n) := by
    rw [hu]
    change qL (algebraMap R (Localization.Away f) (f ^ n)) = φ (qR f ^ n)
    rw [← map_pow qR]
    rfl
  have hinv : φ ((↑u⁻¹ : R ⧸ I) ^ n) *
      qL (algebraMap R (Localization.Away f) (f ^ n)) = 1 := by
    rw [hden, ← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
  have he : qL x * qL (algebraMap R (Localization.Away f) (f ^ n)) = φ (qR r) := by
    rw [← map_mul]
    exact congrArg qL (IsLocalization.Away.sec_spec f x)
  refine ⟨qR r * (↑u⁻¹ : R ⧸ I) ^ n, ?_⟩
  change φ (qR r * (↑u⁻¹ : R ⧸ I) ^ n) = qL x
  rw [map_mul, ← he]
  calc
    qL x * qL (algebraMap R (Localization.Away f) (f ^ n)) * φ ((↑u⁻¹ : R ⧸ I) ^ n) =
        qL x * (φ ((↑u⁻¹ : R ⧸ I) ^ n) * qL (algebraMap R (Localization.Away f) (f ^ n))) := by
          ac_rfl
    _ = qL x := by rw [hinv, mul_one]

/-- The global extension recovers the local ideal, has the identical
center scheme, and has no points on the complement of `D(f)`. -/
theorem supported_affine_center_extension
    (F : Ideal R) (f : R) (hf : 1 - f ∈ F)
    (C : Ideal (Localization.Away f)) (N : ℕ)
    (hC : (F ^ N).map (algebraMap R (Localization.Away f)) ≤ C) :
    let I := C.comap (algebraMap R (Localization.Away f))
    I.map (algebraMap R (Localization.Away f)) = C ∧
      Function.Bijective (Ideal.quotientMap C (algebraMap R (Localization.Away f)) le_rfl) ∧
      ∀ q : Ideal R, q ≠ ⊤ → I ≤ q → f ∉ q := by
  let I := C.comap (algebraMap R (Localization.Away f))
  have hunit := supported_affine_center_parameter_unit F f hf C N hC
  refine ⟨IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) C,
    supported_affine_center_quotientMap_bijective f C hunit, ?_⟩
  intro q hq hIq hfq
  have hpow : (1 - f) ^ N ∈ I := hC (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hf N))
  have hqpow : (1 - f) ^ N ∈ q := hIq hpow
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q hq
  have h1 : (1 : R) ∈ M := by
    have hsub := hM.isPrime.mem_of_pow_mem N (hqM hqpow)
    simpa only [sub_add_cancel] using M.add_mem hsub (hqM hfq)
  exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M h1 isUnit_one)

/-- The extended center is canonically the same affine scheme as the
center originally specified on the principal open. -/
def supportedAffineCenterQuotientEquiv
    (F : Ideal R) (f : R) (hf : 1 - f ∈ F)
    (C : Ideal (Localization.Away f)) (N : ℕ)
    (hC : (F ^ N).map (algebraMap R (Localization.Away f)) ≤ C) :
    (R ⧸ C.comap (algebraMap R (Localization.Away f))) ≃+* (Localization.Away f ⧸ C) :=
  RingEquiv.ofBijective (Ideal.quotientMap C (algebraMap R (Localization.Away f)) le_rfl)
    (supported_affine_center_quotientMap_bijective f C
      (supported_affine_center_parameter_unit F f hf C N hC))

variable {k : Type*} [CommRing k] [Algebra k R]

/-- Smoothness of a center supported inside the isolated stratum survives
its extension from the principal open to the whole affine scheme. -/
theorem supported_affine_center_smooth
    (F : Ideal R) (f : R) (hf : 1 - f ∈ F)
    (C : Ideal (Localization.Away f)) (N : ℕ)
    (hC : (F ^ N).map (algebraMap R (Localization.Away f)) ≤ C)
    [Algebra.Smooth k (Localization.Away f ⧸ C)] :
    Algebra.Smooth k (R ⧸ C.comap (algebraMap R (Localization.Away f))) := by
  let e := supportedAffineCenterQuotientEquiv F f hf C N hC
  let eA : (R ⧸ C.comap (algebraMap R (Localization.Away f))) ≃ₐ[k]
      (Localization.Away f ⧸ C) := AlgEquiv.ofRingEquiv (f := e) (by
    intro a
    change Ideal.Quotient.mk C (algebraMap R (Localization.Away f) (algebraMap k R a)) =
      Ideal.Quotient.mk C (algebraMap k (Localization.Away f) a)
    have hbase := IsScalarTower.algebraMap_apply k R (Localization.Away f) a
    exact congrArg (Ideal.Quotient.mk C) hbase.symm)
  exact Algebra.Smooth.of_equiv eA.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.SupportedAffineCenterExtension.Construction
