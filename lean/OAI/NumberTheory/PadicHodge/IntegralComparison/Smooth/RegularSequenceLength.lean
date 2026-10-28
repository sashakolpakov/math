import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.ConormalRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedImmersionRegularity

/-! # Regular Sequence Length -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequenceLength

noncomputable section

/-! Regular equations for a smooth closed center can be chosen with the
actual codimension, computed at the original point over an arbitrary base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry KaehlerDifferential

universe u

theorem exists_pointed_open_regular_sequence
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (p : PrimeSpectrum (R ⧸ I)) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q =
        p.comap (Ideal.Quotient.mk I) ∧
      ∃ (r : ℕ) (z : Fin r → S) (D : Fin r → Derivation k S S),
        (∀ i j, D i (z j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.ofList (List.ofFn z) ∧
        RingTheory.Sequence.IsRegular S (List.ofFn z) ∧
        r = Module.rankAtStalk Ω[R⁄k] (p.comap (Ideal.Quotient.mk I)) -
          Module.rankAtStalk Ω[R ⧸ I⁄k] p := by
  classical
  have hIp : I ≤ (p.comap (Ideal.Quotient.mk I)).asIdeal := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ p.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.asIdeal.zero_mem
  obtain ⟨S, hSk, hSs, f, hf, q, hq, r, z, D, hD, hI, hreg⟩ :=
    ClosedImmersionRegularity.exists_pointed_open_regular_sequence (k := k) I
      (p.comap (Ideal.Quotient.mk I)) hIp
  let : Algebra R S := f.toRingHom.toAlgebra
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) := hf
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)
      (φ := CommRingCat.ofHom f.toRingHom)).mp inferInstance)
  let J := I.map (algebraMap R S)
  have hJq : J ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have he := congrArg PrimeSpectrum.asIdeal hq
    change I ≤ q.asIdeal.comap f.toRingHom
    change q.asIdeal.comap f.toRingHom = _ at he
    rw [he]
    exact hIp
  let q₀ := J.primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨q, hJq⟩
  have hq₀ : q₀.comap (Ideal.Quotient.mk J) = q :=
    congrArg Subtype.val (J.primeSpectrumQuotientOrderIsoZeroLocus.apply_symm_apply ⟨q, hJq⟩)
  have hp : q₀.comap (algebraMap (R ⧸ I) (S ⧸ J)) = p := by
    apply PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
    calc
      (q₀.comap (algebraMap (R ⧸ I) (S ⧸ J))).comap (Ideal.Quotient.mk I) =
          (q₀.comap (Ideal.Quotient.mk J)).comap (algebraMap R S) := rfl
      _ = p.comap (Ideal.Quotient.mk I) := by rw [hq₀]; exact hq
  have hz : Ideal.span (Set.range z) = J := by
    rw [← RegularSequence.CoordinateRegularity.ofList_ofFn, ← hI]
    rfl
  let v : Fin r → J := fun i => ⟨z i, hz ▸ Ideal.subset_span ⟨i, rfl⟩⟩
  have hn := IntegralComparison.Etale.ConormalRank.cardinal_eq_rank (k := k) I v D hD hz q₀
  rw [Fintype.card_fin, hp] at hn
  refine ⟨S, hSk, hSs, f, hf, q, hq, r, z, D, hD, hI, hreg, ?_⟩
  exact hn.trans (ConormalRank.quotient_rank_sub (k := k) I p)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequenceLength
