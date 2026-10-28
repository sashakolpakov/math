import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Finite Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood.Construction

noncomputable section

section

/-! Detecting an étale isomorphism on a nilpotent quotient, for local Taylor-order comparison. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem ideal_map_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    IsNilpotent (I.map (algebraMap R S)) := by
  obtain ⟨n, hn⟩ := hI
  change I ^ n = ⊥ at hn
  refine ⟨n, ?_⟩
  change (I.map (algebraMap R S)) ^ n = ⊥
  rw [← Ideal.map_pow, hn, Ideal.map_bot]

/-- A formally étale algebra map is an isomorphism if its reduction
modulo a nilpotent ideal is an isomorphism. Existence and uniqueness of
nilpotent lifts construct the inverse. -/
theorem formallyEtale_bijective_of_nilpotent_reduction [Algebra.FormallyEtale R S]
    (I : Ideal R) (hI : IsNilpotent I)
    (hred : Function.Bijective (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))) :
    Function.Bijective (algebraMap R S) := by
  let J := I.map (algebraMap R S)
  let : IsScalarTower R (R ⧸ I) (S ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) (S ⧸ J)) hred
  let g : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  obtain ⟨η, hη⟩ := Algebra.FormallySmooth.exists_lift I hI g
  have hcomp : (Algebra.ofId R S).comp η = AlgHom.id R S := by
    apply Algebra.FormallyUnramified.lift_unique J (ideal_map_isNilpotent I hI)
    apply AlgHom.ext
    intro s
    change Ideal.Quotient.mk J (algebraMap R S (η s)) = Ideal.Quotient.mk J s
    calc
      _ = e (Ideal.Quotient.mk I (η s)) := (e.commutes (η s)).symm
      _ = e (g s) := congrArg e (AlgHom.congr_fun hη s)
      _ = _ := e.apply_symm_apply (Ideal.Quotient.mk J s)
  have hleft : Function.LeftInverse η (algebraMap R S) := fun r => η.commutes r
  refine ⟨hleft.injective, ?_⟩
  intro s
  exact ⟨η s, AlgHom.congr_fun hcomp s⟩

end

/-! Étale maps with identical residue neighborhoods have identical finite-order neighborhoods. -/

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]

theorem formallyEtale_quotient_of_formallyEtale (I : Ideal R) :
    Algebra.FormallyEtale (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm

/-- A formally étale map inducing an isomorphism modulo an ideal also
induces an isomorphism modulo every positive power of that ideal. -/
theorem formallyEtale_bijective_on_finite_neighborhood (I : Ideal R)
    (hred : Function.Bijective (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S))))
    (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (algebraMap (R ⧸ I ^ n) (S ⧸ (I ^ n).map (algebraMap R S))) := by
  let N := I ^ n
  let J := I.map (algebraMap R S)
  let NS := N.map (algebraMap R S)
  let R' := R ⧸ N
  let S' := S ⧸ NS
  let I' := I.map (Ideal.Quotient.mk N)
  let β := algebraMap R' S'
  let : Algebra.FormallyEtale R' S' := formallyEtale_quotient_of_formallyEtale N
  have hnil : IsNilpotent I' := by
    refine ⟨n, ?_⟩
    change (I.map (Ideal.Quotient.mk N)) ^ n = ⊥
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self N
  have hNI : N ≤ I := Ideal.pow_le_self hn
  have hmap : I'.map β = J.map (Ideal.Quotient.mk NS) := by
    change (I.map (Ideal.Quotient.mk N)).map β =
      (I.map (algebraMap R S)).map (Ideal.Quotient.mk NS)
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let eR : (R' ⧸ I') ≃+* R ⧸ I := DoubleQuot.quotQuotEquivQuotOfLE hNI
  let eS : (S' ⧸ I'.map β) ≃+* S ⧸ J :=
    (Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hNI))
  let γ := algebraMap (R' ⧸ I') (S' ⧸ I'.map β)
  let α := algebraMap (R ⧸ I) (S ⧸ J)
  have hcomm : eS.toRingHom.comp γ = α.comp eR.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r'
    rfl
  have hbij : Function.Bijective (eS.toRingHom.comp γ) := by
    rw [hcomm]
    exact hred.comp eR.bijective
  have hγ : Function.Bijective γ := by
    constructor
    · intro x y h
      exact hbij.1 (congrArg eS h)
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 (eS y)
      exact ⟨x, eS.injective hx⟩
  exact formallyEtale_bijective_of_nilpotent_reduction I' hnil hγ

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.FiniteNeighborhood.Construction
