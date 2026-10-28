import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy

/-! # Exterior Coordinate -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate.ExteriorCoordinateProjection

noncomputable section

/-!
# Eliminating exterior coordinates

The coordinate projection kills a wedge containing that coordinate and
fixes the other coordinate wedges. Eliminating every coordinate therefore
annihilates every positive exterior degree, over any coefficient ring.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorContractionCoe.ExteriorContraction OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy Classical

universe u

variable (R σ : Type u) [CommRing R]

def ambient (i : σ) : Module.End R (ExteriorAlgebra R (σ →₀ R)) :=
  LinearMap.id - (LinearMap.mulLeft R (ExteriorAlgebra.ι R (Finsupp.single i 1))).comp
    (ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i))

theorem ambient_one (i : σ) : ambient R σ i 1 = 1 := by
  change 1 - ExteriorAlgebra.ι R (Finsupp.single i 1) *
    ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i) 1 = 1
  rw [ExteriorContractionCoe.ExteriorContraction.ambientContraction_one, mul_zero, sub_zero]

theorem ambient_coordinate_mul (i j : σ) (a : ExteriorAlgebra R (σ →₀ R)) :
    ambient R σ i (ExteriorAlgebra.ι R (Finsupp.single j 1) * a) =
      if j = i then 0 else ExteriorAlgebra.ι R (Finsupp.single j 1) * ambient R σ i a := by
  classical
  change ExteriorAlgebra.ι R (Finsupp.single j 1) * a -
    ExteriorAlgebra.ι R (Finsupp.single i 1) *
      ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i)
        (ExteriorAlgebra.ι R (Finsupp.single j 1) * a) = _
  rw [ExteriorContractionCoe.ExteriorContraction.ambientContraction_ι_mul]
  change _ - ExteriorAlgebra.ι R (Finsupp.single i 1) *
    ((Finsupp.single j (1 : R)) i • a - ExteriorAlgebra.ι R (Finsupp.single j 1) *
      ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i) a) = _
  by_cases hji : j = i
  · subst j
    rw [ite_eq_left rfl, Finsupp.single_eq_same, one_smul, mul_sub,
      ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, sub_zero, sub_self]
  · rw [ite_eq_right hji, Finsupp.single_eq_of_ne (Ne.symm hji), zero_smul, zero_sub,
      mul_neg, sub_neg_eq_add]
    have he := ExteriorAlgebra.ι_add_mul_swap (R := R) (Finsupp.single i (1 : R)) (Finsupp.single j 1)
    have he' : ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) * ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) =
        -(ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) * ExteriorAlgebra.ι R (Finsupp.single i (1 : R))) :=
      eq_neg_of_add_eq_zero_left he
    change _ = ExteriorAlgebra.ι R (Finsupp.single j (1 : R)) *
      (a - ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) *
        ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i) a)
    rw [← mul_assoc, he', neg_mul, mul_sub, mul_assoc, sub_eq_add_neg]

theorem ambient_word (i : σ) (n : ℕ) (v : Fin n → σ) :
    ambient R σ i (ExteriorAlgebra.ιMulti R n (fun k => Finsupp.single (v k) 1)) =
      if i ∈ Set.range v then 0 else ExteriorAlgebra.ιMulti R n (fun k => Finsupp.single (v k) (1 : R)) := by
  classical
  induction n with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, ambient_one]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, ambient_coordinate_mul]
    by_cases hhead : v 0 = i
    · rw [ite_eq_left hhead, ite_eq_left ⟨0, hhead⟩]
    · rw [ite_eq_right hhead]
      change _ * ambient R σ i (ExteriorAlgebra.ιMulti R n (fun k => Finsupp.single (v k.succ) (1 : R))) = _
      rw [ih (fun k => v k.succ)]
      have hrange : i ∈ Set.range v ↔ i ∈ Set.range (fun k : Fin n => v k.succ) := by
        constructor
        · rintro ⟨k, hk⟩
          refine Fin.cases ?_ (fun l hl => ⟨l, hl⟩) k hk
          exact fun h => (hhead h).elim
        · rintro ⟨k, hk⟩
          exact ⟨k.succ, hk⟩
      simp only [hrange]
      split_ifs
      · rw [mul_zero]
      · rfl

theorem projection_coe (i : σ) (n : ℕ) (ω : ⋀[R]^n (σ →₀ R)) :
    (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection R σ i n ω : ExteriorAlgebra R (σ →₀ R)) = ambient R σ i ω := by
  cases n with
  | zero =>
    change (ω : ExteriorAlgebra R (σ →₀ R)) = (ω : ExteriorAlgebra R (σ →₀ R)) -
      ExteriorAlgebra.ι R (Finsupp.single i (1 : R)) *
      ExteriorContractionCoe.ExteriorContraction.ambientContraction R (σ →₀ R) (Finsupp.lapply i) ω
    rw [ExteriorContractionCoe.ExteriorContraction.ambientContraction_degreeZero R (σ →₀ R) (Finsupp.lapply i) ω.property,
      mul_zero, sub_zero]
  | succ n => rfl

theorem projection_word (i : σ) (n : ℕ) (v : Fin n → σ) :
    Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection R σ i n (exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1)) =
      if i ∈ Set.range v then 0 else exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) (1 : R)) := by
  classical
  apply Subtype.ext
  rw [projection_coe]
  change ambient R σ i (ExteriorAlgebra.ιMulti R n (fun k => Finsupp.single (v k) 1)) = _
  rw [ambient_word]
  split_ifs <;> rfl

def successive : List σ → (n : ℕ) → Module.End R (⋀[R]^n (σ →₀ R))
  | [], _ => LinearMap.id
  | i :: l, n => (successive l n).comp (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection R σ i n)

theorem successive_word (l : List σ) (n : ℕ) (v : Fin n → σ) :
    ExteriorCoordinateProjection.successive R σ l n (exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) 1)) =
      if ∃ i ∈ l, i ∈ Set.range v then 0
      else exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) (1 : R)) := by
  induction l with
  | nil => simp [ExteriorCoordinateProjection.successive]
  | cons i l ih =>
    change ExteriorCoordinateProjection.successive R σ l n (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection R σ i n _) = _
    rw [projection_word]
    by_cases hi : i ∈ Set.range v
    · rw [ite_eq_left hi, map_zero, ite_eq_left ⟨i, List.mem_cons_self, hi⟩]
    · rw [ite_eq_right hi, ih]
      congr 1
      simp only [List.mem_cons, exists_eq_or_imp, hi, false_or]

theorem word_span (n : ℕ) :
    Submodule.span R (Set.range (fun v : Fin n → σ =>
      exteriorPower.ιMulti R n (fun k => Finsupp.single (v k) (1 : R)))) = ⊤ := by
  have hb : Submodule.span R (Set.range (fun i : σ => Finsupp.single i (1 : R))) = ⊤ :=
    (Finsupp.basisSingleOne : Module.Basis σ R (σ →₀ R)).span_eq
  have hs := exteriorPower.ιMulti_span_of_span R n (σ →₀ R) hb
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  have hv : ∀ k, ∃ i, Finsupp.single i (1 : R) = a k := fun k => ha (Set.mem_range_self k)
  choose v hv using hv
  apply Submodule.subset_span
  exact ⟨v, congrArg (exteriorPower.ιMulti R n) (funext hv)⟩

theorem successive_positive_eq_zero (l : List σ) (hl : ∀ i, i ∈ l) (n : ℕ) :
    ExteriorCoordinateProjection.successive R σ l (n + 1) = 0 := by
  apply LinearMap.ext_on (word_span R σ (n + 1))
  rintro _ ⟨v, rfl⟩
  rw [successive_word, ite_eq_left ⟨v 0, hl (v 0), 0, rfl⟩]
  rfl

theorem successive_zero (l : List σ) : ExteriorCoordinateProjection.successive R σ l 0 = LinearMap.id := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (ExteriorCoordinateProjection.successive R σ l 0).comp LinearMap.id = LinearMap.id
    rw [ih, LinearMap.id_comp]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate.ExteriorCoordinateProjection
