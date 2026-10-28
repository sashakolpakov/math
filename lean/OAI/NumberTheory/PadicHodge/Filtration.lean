import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear
import OAI.NumberTheory.PadicHodge.ExtremeSlopes

/-! # Filtration -/

namespace OAI.NumberTheory.PadicHodge.Filtration.CM.ExtremeSlopesAdapter

noncomputable section

/-! Filtration and scalar-dimension bridges for the actual GeometricComparison summands. -/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

section Filtration

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A finite filtration supported in weights zero and one has this Hodge number. -/
theorem hodge_number_weight_one (F : GeometricComparison.Linear.FiniteFiltration K V)
    (h0 : F.step 0 = ⊤) (h2 : F.step 2 = ⊥) :
    F.tH = (Module.finrank K (F.step 1) : ℚ) := by
  unfold WeakAdmissibility.FilteredRepresentations.Construction.FiniteFiltration.tH
  rw [finsum_eq_single _ 1 (by
    intro i hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hz : Module.finrank K (F.Graded i) = 0 := by
        rcases lt_or_ge i 0 with hn | hn
        · exact F.graded_finrank_eq_zero_of_lt h0 hn
        · exact F.graded_finrank_eq_zero_of_le h2 (by omega)
      simp [hz])]
  have hr := F.graded_finrank_add 1
  change Module.finrank K (F.Graded 1) + Module.finrank K (F.step 2) = _ at hr
  rw [h2, finrank_bot, add_zero] at hr
  simpa only [Int.cast_one, one_mul] using congrArg (Nat.cast : ℕ → ℚ) hr

/-- The induced filtration step is the actual intersection with the summand. -/
def inducedStepEquiv (S F : Submodule K V) :
    F.comap S.subtype ≃ₗ[K] (S ⊓ F : Submodule K V) where
  toFun x := ⟨x.1.1, x.1.2, x.2⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K V] in
theorem induced_step_finrank (S F : Submodule K V) :
    Module.finrank K (F.comap S.subtype) = Module.finrank K ↥(S ⊓ F) :=
  (inducedStepEquiv S F).finrank_eq

/-- Comparison at every filtration index supplies both endpoint conditions.
Only the finite-dimensional local space is required here. -/
theorem comparison_weight_one
    {C W : Type*} [Field C] [AddCommGroup W] [Module C W]
    (F : GeometricComparison.Linear.FiniteFiltration K V) (S : Submodule K V)
    (B : Submodule C W) (G : ℤ → Submodule C W)
    (hG0 : ∀ i ≤ 0, G i = ⊤) (hG2 : G 2 = ⊥)
    (hcmp : ∀ i : ℤ,
      Module.finrank K ↥(S ⊓ F.step i) = Module.finrank C ↥(B ⊓ G i)) :
    Module.finrank K S = Module.finrank C B ∧
      (F.restrict S).step 0 = ⊤ ∧ (F.restrict S).step 2 = ⊥ := by
  obtain ⟨a, ha⟩ := F.eventually_top
  have htotal := hcmp (min a 0)
  rw [F.step_eq_top ha (min_le_left _ _), hG0 _ (min_le_right _ _),
    inf_top_eq, inf_top_eq] at htotal
  refine ⟨htotal, ?_, ?_⟩
  · apply Submodule.eq_top_of_finrank_eq
    change Module.finrank K ((F.step 0).comap S.subtype) = Module.finrank K S
    rw [induced_step_finrank, hcmp 0, hG0 0 le_rfl, inf_top_eq, htotal]
  · apply Submodule.finrank_eq_zero.mp
    change Module.finrank K ((F.step 2).comap S.subtype) = 0
    rw [induced_step_finrank, hcmp 2, hG2, inf_bot_eq, finrank_bot]

end Filtration

section Coefficients

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L]
  {D : Type*} [AddCommGroup D] [Module K D] [FiniteDimensional K D]

omit [FiniteDimensional K D] in
/-- Restricting a finite coefficient space multiplies every step dimension
by the coefficient degree. -/
theorem coefficient_step_finrank
    (F : GeometricComparison.Linear.FiniteFiltration K D) (S : Submodule L (L ⊗[K] D)) (i : ℤ) :
    Module.finrank K ((GeometricComparison.Linear.coefficientSummandFiltration L F S).step i) =
      Module.finrank K L *
        Module.finrank L ↥(S ⊓ GeometricComparison.Linear.coefficientFiltration L F.step i) := by
  change Module.finrank K
    ((((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step i).restrictScalars K) = _
  rw [((Submodule.restrictScalarsEquiv K L S
    (((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step i)).restrictScalars K).finrank_eq]
  change Module.finrank K (((F.step i).baseChange L).comap S.subtype) = _
  rw [((inducedStepEquiv S ((F.step i).baseChange L)).restrictScalars K).finrank_eq]
  let T : Submodule L (L ⊗[K] D) := S ⊓ (F.step i).baseChange L
  let : AddCommGroup T := inferInstance
  let : Module L T := inferInstance
  let : Module.Free L T := Module.Free.of_divisionRing L T
  exact (Module.finrank_mul_finrank K L T).symm

/-- GeometricComparison's restriction-of-scalars Hodge number has the expected normalization. -/
theorem coefficient_hodge_number
    (F : GeometricComparison.Linear.FiniteFiltration K D) (S : Submodule L (L ⊗[K] D))
    (h0 : ((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step 0 = ⊤)
    (h2 : ((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step 2 = ⊥) :
    let : FiniteDimensional K S := Module.Finite.trans (R := K) L S
    (GeometricComparison.Linear.coefficientSummandFiltration L F S).tH =
      (Module.finrank K L : ℚ) *
        (Module.finrank L ↥(S ⊓ GeometricComparison.Linear.coefficientFiltration L F.step 1) : ℚ) := by
  let : FiniteDimensional K S := Module.Finite.trans (R := K) L S
  have h0' : (GeometricComparison.Linear.coefficientSummandFiltration L F S).step 0 = ⊤ := by
    change (((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step 0).restrictScalars K = ⊤
    rw [h0]
    rfl
  have h2' : (GeometricComparison.Linear.coefficientSummandFiltration L F S).step 2 = ⊥ := by
    change (((GeometricComparison.Linear.finiteCoefficientFiltration L F).restrict S).step 2).restrictScalars K = ⊥
    rw [h2]
    rfl
  rw [hodge_number_weight_one _ h0' h2', coefficient_step_finrank]
  simp only [Nat.cast_mul]

end Coefficients

/-- All numerical consequences needed from a comparison on one actual
coefficient summand. This generic step keeps geometric definitions opaque. -/
theorem coefficient_comparison_numbers
    (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    {D : Type*} [AddCommGroup D] [Module ℚ_[q] D] [FiniteDimensional ℚ_[q] D]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] D)
    (S : Submodule L (L ⊗[ℚ_[q]] D)) (B : Submodule ℂ W)
    (G : ℤ → Submodule ℂ W)
    (φS : S ≃ₗ[L] S)
    (hWA : letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L S
      GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L Fil S) (φS.restrictScalars ℚ_[q]))
    (hG0 : ∀ i ≤ 0, G i = ⊤) (hG2 : G 2 = ⊥)
    (hcmp : ∀ i : ℤ,
      Module.finrank L ↥(S ⊓ GeometricComparison.Linear.coefficientFiltration L Fil.step i) =
      Module.finrank ℂ ↥(B ⊓ G i)) :
    let F := (GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S
    Module.finrank L S = Module.finrank ℂ B ∧
    F.step 0 = ⊤ ∧ F.step 2 = ⊥ ∧
    Module.finrank L (F.step 1) = Module.finrank ℂ ↥(B ⊓ G 1) ∧
    (Padic.valuation (p := q) (LinearMap.det (A := ℚ_[q]) (M := S) (φS.restrictScalars ℚ_[q]).toLinearMap) : ℚ) =
      (Module.finrank ℚ_[q] L : ℚ) * (Module.finrank ℂ ↥(B ⊓ G 1) : ℚ) := by
  obtain ⟨hDim, h0, h2⟩ := comparison_weight_one
    (GeometricComparison.Linear.finiteCoefficientFiltration L Fil) S B G hG0 hG2 hcmp
  have h1 : Module.finrank L (((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 1) =
      Module.finrank ℂ ↥(B ⊓ G 1) := by
    exact (induced_step_finrank S ((Fil.step 1).baseChange L)).trans (hcmp 1)
  refine ⟨hDim, h0, h2, h1, ?_⟩
  let : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L S
  have hn := hWA.1.symm
  rw [coefficient_hodge_number L Fil S h0 h2, hcmp 1] at hn
  exact hn

/-- Newton numbers on the whole module and every stable subspace. Values on
unstable subspaces are irrelevant to weak admissibility and set to zero. -/
def summandNewton (q : ℕ) [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module ℚ_[q] V]
    (φ : V ≃ₗ[ℚ_[q]] V) (S : Submodule ℚ_[q] V) : ℚ := by
  classical
  exact if S = ⊤ then (Padic.valuation (p := q) φ.toLinearMap.det : ℚ)
    else if hS : S ≤ S.comap φ.toLinearMap then
      (Padic.valuation (p := q) (φ.toLinearMap.restrict hS).det : ℚ)
    else 0

/-- The raw GeometricComparison weak-admissibility inequalities become exactly the numerical
interface of the checked ExtremeSlopes proof once the endpoint filtration bounds hold. -/
theorem weaklyAdmissible01_of_finite_filtration
    (q : ℕ) [Fact q.Prime]
    {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]
    (F : GeometricComparison.Linear.FiniteFiltration ℚ_[q] V) (φ : V ≃ₗ[ℚ_[q]] V)
    (h0 : F.step 0 = ⊤) (h2 : F.step 2 = ⊥)
    (hWA : GeometricComparison.Linear.WeaklyAdmissible q F φ) :
    ExtremeSlopes.CM.Construction.WeaklyAdmissible01 (F.step 1) φ.toLinearMap (summandNewton q φ) := by
  classical
  have hH := hodge_number_weight_one F h0 h2
  refine ⟨?_, ?_⟩
  · simpa [summandNewton] using hH.symm.trans hWA.1
  · intro S hS
    have hS' : S ≤ S.comap φ.toLinearMap := hS
    by_cases htop : S = ⊤
    · subst S
      rw [top_inf_eq]
      simpa [summandNewton] using (hH.symm.trans hWA.1).le
    · have h := hWA.2 S hS'
      have hS0 : (F.restrict S).step 0 = ⊤ := by
        change (F.step 0).comap S.subtype = ⊤
        rw [h0, Submodule.comap_top]
      have hS2 : (F.restrict S).step 2 = ⊥ := by
        change (F.step 2).comap S.subtype = ⊥
        rw [h2, Submodule.comap_bot, Submodule.ker_subtype]
      rw [hodge_number_weight_one (F.restrict S) hS0 hS2] at h
      change (Module.finrank ℚ_[q] ((F.step 1).comap S.subtype) : ℚ) ≤ _ at h
      rw [induced_step_finrank] at h
      simpa only [summandNewton, ite_eq_right htop, dite_eq_left hS'] using h

/-- Exact scalar-restriction dimension formula for any coefficient subspace. -/
theorem restricted_submodule_finrank
    {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (S : Submodule L V) :
    Module.finrank K (S.restrictScalars K) =
      Module.finrank K L * Module.finrank L S := by
  rw [((Submodule.restrictScalarsEquiv K L V S).restrictScalars K).finrank_eq]
  let : AddCommGroup S := inferInstance
  let : Module L S := inferInstance
  let : Module.Free L S := Module.Free.of_divisionRing L S
  exact (Module.finrank_mul_finrank K L S).symm

/-- Normalize rational Newton numbers by the coefficient-field degree. -/
def normalizedSummandNewton (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [Module ℚ_[q] V]
    [IsScalarTower ℚ_[q] L V]
    (φ : V ≃ₗ[L] V) (S : Submodule L V) : ℚ :=
  summandNewton q (φ.restrictScalars ℚ_[q]) (S.restrictScalars ℚ_[q]) /
    (Module.finrank ℚ_[q] L : ℚ)

/-- The numerical weak-admissibility interface over L follows from the
rational one by scalar restriction and division by the positive degree. -/
theorem normalized_weaklyAdmissible01
    (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    [Module ℚ_[q] V] [IsScalarTower ℚ_[q] L V]
    (F1 : Submodule L V) (φ : V ≃ₗ[L] V)
    (hWA : letI : FiniteDimensional ℚ_[q] V := Module.Finite.trans (R := ℚ_[q]) L V
      ExtremeSlopes.CM.Construction.WeaklyAdmissible01 (F1.restrictScalars ℚ_[q])
        (φ.restrictScalars ℚ_[q]).toLinearMap (summandNewton q (φ.restrictScalars ℚ_[q]))) :
    ExtremeSlopes.CM.Construction.WeaklyAdmissible01 F1 φ.toLinearMap (normalizedSummandNewton q L φ) := by
  let : FiniteDimensional ℚ_[q] V := Module.Finite.trans (R := ℚ_[q]) L V
  have hd : 0 < (Module.finrank ℚ_[q] L : ℚ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ_[q] L)
  have hr (S : Submodule L V) :
      (Module.finrank ℚ_[q] (S.restrictScalars ℚ_[q]) : ℚ) =
        (Module.finrank ℚ_[q] L : ℚ) * (Module.finrank L S : ℚ) := by
    exact_mod_cast restricted_submodule_finrank L S
  refine ⟨?_, ?_⟩
  · change (Module.finrank L F1 : ℚ) = _ / _
    rw [Submodule.restrictScalars_top]
    apply (eq_div_iff hd.ne').mpr
    have he := hWA.1
    rw [hr F1] at he
    nlinarith
  · intro S hS
    have hS' : ∀ x ∈ S.restrictScalars ℚ_[q],
        (φ.restrictScalars ℚ_[q]) x ∈ S.restrictScalars ℚ_[q] := hS
    have he := hWA.2 (S.restrictScalars ℚ_[q]) hS'
    rw [← Submodule.restrictScalars_inf, hr (S ⊓ F1)] at he
    apply (le_div_iff₀ hd).mpr
    nlinarith

/-- GeometricComparison's actual coefficient-summand filtration supplies ExtremeSlopes's
coefficient-normalized numerical weak admissibility. -/
theorem coefficient_weaklyAdmissible01
    (q : ℕ) [Fact q.Prime]
    (L : Type*) [Field L] [Algebra ℚ_[q] L] [FiniteDimensional ℚ_[q] L]
    {D : Type*} [AddCommGroup D] [Module ℚ_[q] D] [FiniteDimensional ℚ_[q] D]
    (Fil : GeometricComparison.Linear.FiniteFiltration ℚ_[q] D) (S : Submodule L (L ⊗[ℚ_[q]] D))
    (φS : S ≃ₗ[L] S)
    (hWA : letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L S
      GeometricComparison.Linear.WeaklyAdmissible q (GeometricComparison.Linear.coefficientSummandFiltration L Fil S) (φS.restrictScalars ℚ_[q]))
    (h0 : ((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 0 = ⊤)
    (h2 : ((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 2 = ⊥) :
    ExtremeSlopes.CM.Construction.WeaklyAdmissible01 (K := L) (D := S)
      (((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 1)
      φS.toLinearMap (normalizedSummandNewton q L (V := S) φS) := by
  let : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L S
  apply normalized_weaklyAdmissible01 q L (V := S) _ φS
  apply weaklyAdmissible01_of_finite_filtration q (V := S)
    (GeometricComparison.Linear.coefficientSummandFiltration L Fil S) (φS.restrictScalars ℚ_[q]) _ _ hWA
  · change (((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 0).restrictScalars ℚ_[q] = ⊤
    rw [h0, Submodule.restrictScalars_top]
  · change (((GeometricComparison.Linear.finiteCoefficientFiltration L Fil).restrict S).step 2).restrictScalars ℚ_[q] = ⊥
    rw [h2, Submodule.restrictScalars_bot]

end

end OAI.NumberTheory.PadicHodge.Filtration.CM.ExtremeSlopesAdapter
