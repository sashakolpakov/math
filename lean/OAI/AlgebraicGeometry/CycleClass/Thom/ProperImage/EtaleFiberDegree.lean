import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Etale Fiber Degree -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleFiberDegree.Constructions.Construction

noncomputable section

open scoped TensorProduct

/-- A finite etale algebra over a separably closed field has one field
factor for each prime, so its dimension counts its geometric points. -/
theorem card_spectrum_eq_finrank_of_etale
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsSepClosed K] [Module.Finite K A] [Algebra.FormallyEtale K A] :
    Nat.card (PrimeSpectrum A) = Module.finrank K A := by
  let : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  rw [(Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

/-- A finite flat algebra over a domain has the same rank at every
field-valued point, including the generic point. -/
theorem finrank_field_baseChange
    (R A K : Type*) [CommRing R] [IsDomain R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [Module.Finite R A] [Module.Flat R A] :
    Module.finrank K (K ⊗[R] A) = Module.finrank R A := by
  let p : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  calc
    Module.finrank K (K ⊗[R] A) = Module.rankAtStalk (K ⊗[R] A) p :=
      (congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[R] A)) p).symm
    _ = Module.rankAtStalk A (p.comap (algebraMap R K)) :=
      Module.rankAtStalk_baseChange (M := A) p
    _ = Module.finrank R A := by
      rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]

/-- The geometric fibers of a finite etale algebra over a domain have
cardinality equal to its generic rank. -/
theorem card_etale_fiber_eq_rank
    (R A K : Type*) [CommRing R] [IsDomain R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [Module.Finite R A] [Algebra.Etale R A]
    [IsSepClosed K] :
    Nat.card (PrimeSpectrum (K ⊗[R] A)) = Module.finrank R A := by
  rw [card_spectrum_eq_finrank_of_etale K, finrank_field_baseChange]

/-- The characters of a finite etale algebra over a separably closed
field are precisely its field factors. -/
def spectrumCharacterEquiv
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsSepClosed K] [Module.Finite K A] [Algebra.FormallyEtale K A] :
    PrimeSpectrum A ≃ (A →ₐ[K] K) := by
  classical
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  let v : PrimeSpectrum A → (A →ₐ[K] K) :=
    fun p => (Pi.evalAlgHom K (fun _ : PrimeSpectrum A => K) p).comp e.toAlgHom
  apply Equiv.ofBijective v
  constructor
  · intro p q hpq
    by_contra hne
    have hv := congrArg (fun k : A →ₐ[K] K => k (e.symm (Pi.single p 1))) hpq
    change e (e.symm (Pi.single p 1)) p = e (e.symm (Pi.single p 1)) q at hv
    simp [Ne.symm hne] at hv
  · intro f
    refine ⟨(⊥ : PrimeSpectrum K).comap f.toRingHom, ?_⟩
    ext a
    change e a ((⊥ : PrimeSpectrum K).comap f.toRingHom) = f a
    exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap f a ⊥).trans
      (Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply _ _)

theorem card_characters_eq_finrank_of_etale
    (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsSepClosed K] [Module.Finite K A] [Algebra.FormallyEtale K A] :
    Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  exact (Nat.card_congr (spectrumCharacterEquiv K A)).symm.trans
    (card_spectrum_eq_finrank_of_etale K A)

/-- The number of lifts of a geometric point through a finite etale
algebra is its generic rank. The lifts are actual algebra homomorphisms. -/
theorem card_etale_point_lifts
    (R A K : Type*) [CommRing R] [IsDomain R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] [Module.Finite R A] [Algebra.Etale R A]
    [IsSepClosed K] :
    Nat.card (A →ₐ[R] K) = Module.finrank R A := by
  rw [Nat.card_congr (AlgHom.liftEquiv R K A K),
    card_characters_eq_finrank_of_etale K, finrank_field_baseChange]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleFiberDegree.Constructions.Construction
