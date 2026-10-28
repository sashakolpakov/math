import OAI.RepresentationTheory.Weil.Local.FiniteQuadraticPieces

/-! # Finite Quadratic Phase -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! The eighth-root phase theorem for every nonzero finite quadratic Gauss sum. -/

open scoped Classical

universe u

theorem FiniteQuadratic.Construction.QuadraticCharacter.phase_gauss_eighth {A : Type u} [AddCommGroup A] [Fintype A]
    (q : FiniteQuadratic.Construction.QuadraticCharacter A) (hq : q.gauss ≠ 0) : FunctionsMetaplectic.Construction.phase q.gauss ^ 8 = 1 := by
  induction hcard : Fintype.card A using Nat.strong_induction_on generalizing A with
  | h n ih =>
    rcases subsingleton_or_nontrivial A with hs | hn
    · let : Subsingleton A := hs
      have hv : ∀ x : A, q x = 1 := fun x => (Subsingleton.elim x 0) ▸ q.map_zero
      simp [FiniteQuadratic.Construction.QuadraticCharacter.gauss, hv, FunctionsMetaplectic.Construction.phase]
    · let : Nontrivial A := hn
      by_cases hani : ∀ x, q x = 1 → x = 0
      · obtain ⟨H, hH, hnd, hphase⟩ := q.anisotropic_has_phase_piece hq hani
        let : Nontrivial H := hH
        have hlt : Fintype.card (q.orthogonal H) < n := by
          rw [← hcard]
          exact q.orthogonal_card_lt H hnd
        have hnz : (q.restrict (q.orthogonal H)).gauss ≠ 0 := by
          rw [q.gauss_orthogonalSplit H hnd] at hq
          exact (mul_ne_zero_iff.mp hq).2
        rw [q.phase_orthogonalSplit H hnd, mul_pow, hphase]
        simpa only [one_mul] using ih _ hlt (q.restrict (q.orthogonal H)) hnz rfl
      · push Not at hani
        obtain ⟨x, hqx, hx⟩ := hani
        let H := AddSubgroup.zmultiples x
        let : Nontrivial H := ⟨⟨⟨x, AddSubgroup.mem_zmultiples x⟩, 0,
          fun h => hx (congrArg Subtype.val h)⟩⟩
        have hH : q.Isotropic H := q.isotropic_zmultiples hqx
        have hlt : Fintype.card (q.orthogonal H ⧸ H.addSubgroupOf (q.orthogonal H)) < n := by
          rw [← hcard]
          exact q.isotropicReduction_card_lt H hH
        have hnz : (q.isotropicReduction H hH).gauss ≠ 0 := by
          rw [q.gauss_isotropicReduction H hH] at hq
          exact (mul_ne_zero_iff.mp hq).2
        rw [q.phase_isotropicReduction H hH]
        exact ih _ hlt (q.isotropicReduction H hH) hnz rfl

end

end OAI.RepresentationTheory.Weil.Local
