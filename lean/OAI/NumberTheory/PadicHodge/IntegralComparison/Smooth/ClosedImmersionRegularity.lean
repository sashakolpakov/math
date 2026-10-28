import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame

/-! # Closed Immersion Regularity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedImmersionRegularity

noncomputable section

/-! A smooth closed center in a smooth algebra has actual regular generators
on an open neighborhood of every point, over an arbitrary base ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_pointed_open_regular_sequence
    {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]
    [IsNoetherianRing R] (I : Ideal R) [Algebra.Smooth k (R ⧸ I)]
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    ∃ (S : CommRingCat.{u}) (_ : Algebra k S) (_ : Algebra.Smooth k S)
      (f : R →ₐ[k] S), IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
      ∃ (q : PrimeSpectrum S), PrimeSpectrum.comap f.toRingHom q = p ∧
      ∃ (r : ℕ) (z : Fin r → S) (D : Fin r → Derivation k S S),
        (∀ i j, D i (z j) = if i = j then 1 else 0) ∧
        I.map f.toRingHom = Ideal.ofList (List.ofFn z) ∧
        RingTheory.Sequence.IsRegular S (List.ofFn z) := by
  classical
  obtain ⟨S, hSk, hSs, f, hf, q, hq, ι, hι, hdec, v, E, hE, hI⟩ :=
    AlgebraicGeometry.Resolution.Blowups.Smooth.CenterPointedFrame.Construction.smooth_center_pointed_open_frame (k := k) I p hIp
  let e := (Fintype.equivFin ι).symm
  let z : Fin (Fintype.card ι) → S := fun i => v (e i)
  let D : Fin (Fintype.card ι) → Derivation k S S := fun i => E (e i)
  have hD (i j : Fin (Fintype.card ι)) : D i (z j) = if i = j then 1 else 0 := by
    simpa only [D, z, Equiv.apply_eq_iff_eq] using hE (e i) (e j)
  have hrange : Set.range z = Set.range v := by
    exact e.surjective.range_comp v
  have hideal : I.map f.toRingHom = Ideal.ofList (List.ofFn z) := by
    rw [RegularSequence.CoordinateRegularity.ofList_ofFn, hrange, hI]
  have hIq : I.map f.toRingHom ≤ q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    have he := congrArg PrimeSpectrum.asIdeal hq
    change q.asIdeal.comap f.toRingHom = p.asIdeal at he
    rwa [he]
  have hproper : Ideal.span (Set.range z) ≠ ⊤ := by
    rw [hrange, ← hI]
    exact ne_top_of_le_ne_top q.isPrime.ne_top hIq
  exact ⟨S, hSk, hSs, f, hf, q, hq, Fintype.card ι, z, D, hD, hideal,
    RegularSequence.CoordinateRegularity.family_isRegular z D hD hproper⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedImmersionRegularity
