import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Principal
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Colon

/-! # Principal Neighborhood Eq -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Quotients.FiniteDescent.PrincipalNeighborhoodEq.Construction.PrincipalNeighborhood

/-! Spreading a principal ideal in a local ring to a principal affine neighborhood. -/

variable {R : Type*} [CommRing R]

theorem exists_mul_le (I J : Ideal R) (hI : I.FG) (p : Ideal R) [p.IsPrime]
    (hle : I.map (algebraMap R (Localization.AtPrime p)) ≤
      J.map (algebraMap R (Localization.AtPrime p))) :
    ∃ s ∉ p, ∀ x ∈ I, s * x ∈ J := by
  classical
  obtain ⟨t, ht⟩ := hI
  have hg (x : t) : ∃ s ∉ p, s * (x : R) ∈ J := by
    have hx : (x : R) ∈ I := ht ▸ Ideal.subset_span x.2
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) J x).mp (hle (Ideal.mem_map_of_mem _ hx))
  choose s hs hsm using hg
  let c := ∏ x : t, s x
  have hc : c ∉ p := by
    simp only [c, Ideal.IsPrime.prod_mem_iff, not_exists, not_and]
    exact fun x _ => hs x
  have hcol : I ≤ J.colon (Ideal.span {c}) := by
    rw [← ht, Ideal.span_le]
    intro x hx
    apply Ideal.mem_colon_span_singleton.mpr
    have hd : s ⟨x, hx⟩ ∣ c := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨d, hd⟩ := hd
    rw [hd]
    simpa [mul_comm, mul_left_comm, mul_assoc] using J.mul_mem_left d (hsm ⟨x, hx⟩)
  exact ⟨c, hc, fun x hx => by
    simpa [Ideal.mem_colon_span_singleton, mul_comm] using hcol hx⟩

theorem exists_away_eq_span (I : Ideal R) (hI : I.FG) (p : Ideal R) [p.IsPrime]
    (a : R) (ha : a ∈ I)
    (hpa : I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R (Localization.AtPrime p) a}) :
    ∃ s ∉ p, I.map (algebraMap R (Localization.Away s)) =
      Ideal.span {algebraMap R (Localization.Away s) a} := by
  obtain ⟨s, hs, hmul⟩ := exists_mul_le I (Ideal.span {a}) hI p (by
    simpa [Ideal.map_span] using hpa.le)
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap R (Localization.Away s) x ∈
      Ideal.span {algebraMap R (Localization.Away s) a}
    have hm := Ideal.mem_map_of_mem (algebraMap R (Localization.Away s)) (hmul x hx)
    rw [Ideal.map_span, Set.image_singleton, map_mul] at hm
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.Away.algebraMap_isUnit s)).mp hm
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ ha

theorem exists_away_isPrincipal [IsDomain R] (I : Ideal R) (hI : I.FG)
    (p : Ideal R) [p.IsPrime]
    (hp : (I.map (algebraMap R (Localization.AtPrime p))).IsPrincipal) :
    ∃ s ∉ p, (I.map (algebraMap R (Localization.Away s))).IsPrincipal := by
  obtain ⟨c, hc⟩ := hp
  change I.map (algebraMap R (Localization.AtPrime p)) = Ideal.span {c} at hc
  have hgen : ∃ a ∈ I, I.map (algebraMap R (Localization.AtPrime p)) =
      Ideal.span {algebraMap R (Localization.AtPrime p) a} := by
    by_cases hz : c = 0
    · exact ⟨0, I.zero_mem, by simpa [hz] using hc⟩
    · obtain ⟨a, ha, he⟩ := Principal.Construction.PrincipalDescent.exists_generator_of_map I hz hc
      exact ⟨a, ha, hc.trans he.symm⟩
  obtain ⟨a, ha, hpa⟩ := hgen
  obtain ⟨s, hs, he⟩ := exists_away_eq_span I hI p a ha hpa
  exact ⟨s, hs, ⟨algebraMap R (Localization.Away s) a, he⟩⟩

end AlgebraicGeometry.Quotients.FiniteDescent.PrincipalNeighborhoodEq.Construction.PrincipalNeighborhood

namespace AlgebraicGeometry.Quotients.FiniteDescent.PrincipalNeighborhoodEq.Construction.PrincipalTransport

/-! Transport of principal extended ideals and their affine neighborhoods. -/

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

theorem map_algHom (I : Ideal R) (g : A →ₐ[R] B)
    (h : (I.map (algebraMap R A)).IsPrincipal) :
    (I.map (algebraMap R B)).IsPrincipal := by
  obtain ⟨a, ha⟩ := h
  change I.map (algebraMap R A) = Ideal.span {a} at ha
  refine ⟨g a, ?_⟩
  change I.map (algebraMap R B) = Ideal.span {g a}
  rw [← g.comp_algebraMap, ← Ideal.map_map, ha, Ideal.map_span, Set.image_singleton]
  rfl

theorem exists_away_isPrincipal [IsDomain R] (I : Ideal R) (hI : I.FG)
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p]
    (h : (I.map (algebraMap R A)).IsPrincipal) :
    ∃ s ∉ p, (I.map (algebraMap R (Localization.Away s))).IsPrincipal := by
  apply PrincipalNeighborhood.exists_away_isPrincipal I hI p
  exact map_algHom I (IsLocalization.algEquiv p.primeCompl A
    (Localization.AtPrime p)).toAlgHom h

end AlgebraicGeometry.Quotients.FiniteDescent.PrincipalNeighborhoodEq.Construction.PrincipalTransport

end

end OAI
