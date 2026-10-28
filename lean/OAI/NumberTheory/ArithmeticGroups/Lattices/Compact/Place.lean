import OAI.NumberTheory.ArithmeticGroups.Lattices.Laurent
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Place -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Place.Construction

noncomputable section

/-! A compact real realization has no nontrivial algebraic cocharacters.
This is an unconditional proof of the anisotropy implication used in Lattices. -/

open scoped Classical

variable {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)

theorem cocharacter_entry_eq_laurent (c : G.Cocharacter)
    {K : Type} [Field K] (ι : k →+* K) (t : Kˣ) (i j : Fin n) :
    (c.hom K ι t).val i j =
      LaurentPolynomial.eval₂ ι t (Laurent.Construction.laurentOfPair (c.coordinates i j)) :=
  (c.coordinate_eq K ι t i j).trans (Laurent.Construction.eval_laurentOfPair ι t _).symm

theorem cocharacter_real_entry_bounded (v : k →+* ℝ)
    [CompactSpace (G.Points v)] (c : G.Cocharacter) (i j : Fin n) :
    ∃ B : ℝ, ∀ t : ℝˣ,
      |LaurentPolynomial.eval₂ v t (Laurent.Construction.laurentOfPair (c.coordinates i j))| ≤ B := by
  have hc : Continuous (fun g : G.Points v => |g.val i j|) := by fun_prop
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hc.continuousOn
  refine ⟨B, fun t => ?_⟩
  rw [← cocharacter_entry_eq_laurent]
  exact hB (Set.mem_image_of_mem _ (Set.mem_univ (c.hom ℝ v t)))

/-- Compact real points force every k-defined algebraic cocharacter to be
trivial over every extension field, by coefficient descent through v. -/
theorem cocharacter_trivial_of_compact_real (v : k →+* ℝ)
    [CompactSpace (G.Points v)] (c : G.Cocharacter)
    (K : Type) [Field K] (ι : k →+* K) : c.hom K ι = 1 := by
  apply MonoidHom.ext
  intro t
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hc := Laurent.Construction.laurent_constant_of_real_bound v (Laurent.Construction.laurentOfPair (c.coordinates i j))
    (cocharacter_real_entry_bounded G v c i j)
  calc
    (c.hom K ι t).val i j =
        LaurentPolynomial.eval₂ ι t (Laurent.Construction.laurentOfPair (c.coordinates i j)) :=
      cocharacter_entry_eq_laurent G c ι t i j
    _ = LaurentPolynomial.eval₂ ι 1 (Laurent.Construction.laurentOfPair (c.coordinates i j)) := by
      rw [hc, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_C]
    _ = (c.hom K ι 1).val i j := (cocharacter_entry_eq_laurent G c ι 1 i j).symm
    _ = _ := by rw [map_one]; rfl

/-- The compact-real-place criterion, with no lattice theorem assumed. -/
theorem anisotropic_of_compact_real_place (S : Algebraic.ConnectedSemisimpleKGroup k)
    (v : k →+* ℝ) (hv : Algebraic.IsCompactAtRealPlace S v) : Algebraic.IsAnisotropic S := by
  let : CompactSpace (S.matrixGroup.Points v) := hv
  intro c K _ ι
  exact cocharacter_trivial_of_compact_real S.matrixGroup v c K ι

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Place.Construction
