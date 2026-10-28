import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots

/-! # PD Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PDForms.FinitePDForms

noncomputable section

/-!
# Generators and degree bounds for divided-power forms

If coordinate differentials span the PD one-forms, then coordinate
differential symbols span every higher degree. With finitely many
coordinates, alternation makes forms vanish above their number.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I) {σ : Type u} (x : σ → A)
  (hspan : Submodule.span A (Set.range (fun i => PD.OneForms.PDOneForms.D R A I δ (x i))) = ⊤)

def coordinateSpan (n : ℕ) : Submodule A (PD.DeRham.PDDeRham.Form R A I δ n) :=
  Submodule.span A (Set.range (fun t : Fin n → σ => PD.DeRham.PDDeRham.symbol R A I δ 1 (x ∘ t)))

include hspan in
theorem symbol_mem_coordinateSpan (n : ℕ) (v : Fin n → A) :
    PD.DeRham.PDDeRham.symbol R A I δ 1 v ∈ coordinateSpan R A I δ x n := by
  classical
  have h (s : Finset (Fin n)) : ∀ v : Fin n → A,
      (∀ j, j ∉ s → ∃ k, v j = x k) →
        PD.DeRham.PDDeRham.symbol R A I δ 1 v ∈ coordinateSpan R A I δ x n := by
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      choose t ht using fun j => hv j (Finset.notMem_empty j)
      have he : v = x ∘ t := funext ht
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self t)
    | @insert i s hi ih =>
      intro v hv
      let L := PD.OneForms.PDOneForms.lift R A I δ (PD.DeRham.PDDeRham.Form R A I δ n)
        (PD.FormSlots.PDFormSlots.derivation R A I δ v i)
        (fun m _ ha => PD.FormSlots.PDFormSlots.derivation_dpow R A I δ v i m ha)
      have hL : Submodule.span A (Set.range (fun k => PD.OneForms.PDOneForms.D R A I δ (x k))) ≤
          (coordinateSpan R A I δ x n).comap L := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k, rfl⟩
        change L (PD.OneForms.PDOneForms.D R A I δ (x k)) ∈ coordinateSpan R A I δ x n
        rw [PD.OneForms.PDOneForms.lift_D]
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨k, Function.update_self i (x k) v⟩
        · obtain ⟨l, hl⟩ := hv j (by simp [hji, hj])
          exact ⟨l, (Function.update_of_ne hji (x k) v).trans hl⟩
      have hv' : PD.OneForms.PDOneForms.D R A I δ (v i) ∈
          Submodule.span A (Set.range (fun k => PD.OneForms.PDOneForms.D R A I δ (x k))) := by
        rw [hspan]
        exact Submodule.mem_top
      have hz := hL hv'
      change L (PD.OneForms.PDOneForms.D R A I δ (v i)) ∈ coordinateSpan R A I δ x n at hz
      rw [PD.OneForms.PDOneForms.lift_D] at hz
      simpa only [PD.FormSlots.PDFormSlots.derivation_apply, Function.update_eq_self] using hz
  exact h Finset.univ v (fun j hj => (hj (Finset.mem_univ j)).elim)

include hspan in
/-- Coordinate differential symbols span every degree of PD forms. -/
theorem coordinateSpan_eq_top (n : ℕ) : coordinateSpan R A I δ x n = ⊤ := by
  apply top_unique
  intro ω hω
  clear hω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (PD.DeRham.PDDeRham.relations R A I δ n) ω
  obtain ⟨ω, rfl⟩ := Submodule.mkQ_surjective (DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction ω using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (coordinateSpan R A I δ x n).zero_mem
  | add a b ha hb =>
    simpa only [map_add] using (coordinateSpan R A I δ x n).add_mem ha hb
  | single v a =>
    change PD.DeRham.PDDeRham.symbol R A I δ a v ∈ coordinateSpan R A I δ x n
    rw [PD.DeRham.PDDeRham.symbol_smul_one]
    exact (coordinateSpan R A I δ x n).smul_mem a (symbol_mem_coordinateSpan R A I δ x hspan n v)

include hspan in
/-- There are no PD forms in degrees above the number of coordinate differentials. -/
theorem higher_form_eq_zero [Fintype σ] (n : ℕ) (hn : Fintype.card σ < n)
    (ω : PD.DeRham.PDDeRham.Form R A I δ n) : ω = 0 := by
  classical
  have hz : coordinateSpan R A I δ x n ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    have hni : ¬ Function.Injective t := by
      intro ht
      have hc := Fintype.card_le_of_injective t ht
      simp only [Fintype.card_fin] at hc
      omega
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hni
    exact PD.DeRham.PDDeRham.symbol_alt R A I δ (x ∘ t) i j (congrArg x hij) hne
  have hm : ω ∈ coordinateSpan R A I δ x n := by
    rw [coordinateSpan_eq_top R A I δ x hspan]
    exact Submodule.mem_top
  exact hz hm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PDForms.FinitePDForms
