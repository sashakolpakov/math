import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentSections

/-! # Sector To -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo.Dolbeault

noncomputable section

section

/-! Coordinate domains and coordinate inversions for finite Laurent sectors. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def laurentCoordinateOpens (s : Finset ι) (i : ι) : Opens ℂ :=
  if i ∈ s then PuncturedCauchy.Dolbeault.puncturedComplexOpen else ⊤

def laurentCoordinateDomain (s : Finset ι) : Opens (ι → ℂ) :=
  DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (laurentCoordinateOpens s)

theorem mem_laurentCoordinateDomain (s : Finset ι) (x : ι → ℂ) :
    x ∈ laurentCoordinateDomain s ↔ ∀ i ∈ s, x i ≠ 0 := by
  rw [laurentCoordinateDomain, DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc]
  constructor
  · intro h i hi
    simpa only [laurentCoordinateOpens, ite_eq_left hi, PuncturedCauchy.Dolbeault.puncturedComplexOpen, Opens.mem_mk,
      Set.mem_ofPred_eq] using h i
  · intro h i
    by_cases hi : i ∈ s
    · simpa only [laurentCoordinateOpens, ite_eq_left hi, PuncturedCauchy.Dolbeault.puncturedComplexOpen, Opens.mem_mk,
        Set.mem_ofPred_eq] using h i hi
    · simp only [laurentCoordinateOpens, ite_eq_right hi, Opens.mem_top]

theorem laurentCoordinateDomain_empty : laurentCoordinateDomain (∅ : Finset ι) = ⊤ := by
  ext x
  change (x ∈ laurentCoordinateDomain (∅ : Finset ι)) ↔ (x ∈ (⊤ : Opens (ι → ℂ)))
  rw [mem_laurentCoordinateDomain]
  simp

omit [Fintype ι] in
theorem laurentCoordinateOpens_update_punctured (s : Finset ι) (i : ι) :
    Function.update (laurentCoordinateOpens s) i PuncturedCauchy.Dolbeault.puncturedComplexOpen = laurentCoordinateOpens (insert i s) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, laurentCoordinateOpens, Finset.mem_insert_self, ite_true]
  · simp only [Function.update_of_ne hji, laurentCoordinateOpens, Finset.mem_insert, hji, false_or]

omit [Fintype ι] in
theorem laurentCoordinateOpens_update_full (s : Finset ι) (i : ι) (hi : i ∉ s) :
    Function.update (laurentCoordinateOpens s) i ⊤ = laurentCoordinateOpens s := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, laurentCoordinateOpens, ite_eq_right hi]
  · exact Function.update_of_ne hji _ _

def laurentInverseCoordinates (s : Finset ι) (x : ι → ℂ) : ι → ℂ :=
  fun i => if i ∈ s then (x i)⁻¹ else x i

omit [Fintype ι] in
theorem laurentInverseCoordinates_involutive (s : Finset ι) (x : ι → ℂ) :
    laurentInverseCoordinates s (laurentInverseCoordinates s x) = x := by
  funext i
  by_cases hi : i ∈ s <;> simp only [laurentInverseCoordinates, hi, ite_true, ite_false, inv_inv]

omit [Fintype ι] in
theorem laurentInverseCoordinates_insert (s : Finset ι) (i : ι) (hi : i ∉ s) (x : ι → ℂ) :
    laurentInverseCoordinates (insert i s) x = laurentInverseCoordinates s (Function.update x i (x i)⁻¹) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [laurentInverseCoordinates, Finset.mem_insert_self, ite_true, ite_eq_right hi, Function.update_self]
  · simp only [laurentInverseCoordinates, Finset.mem_insert, hji, false_or, Function.update_of_ne hji]

theorem laurentInverseCoordinates_mapsTo (s t : Finset ι) :
    MapsTo (laurentInverseCoordinates t) (laurentCoordinateDomain s : Set (ι → ℂ))
      (laurentCoordinateDomain s : Set (ι → ℂ)) := by
  intro x hx
  apply (mem_laurentCoordinateDomain s _).mpr
  intro i hi
  have hxi := (mem_laurentCoordinateDomain s x).mp hx i hi
  by_cases hit : i ∈ t
  · simpa only [laurentInverseCoordinates, ite_eq_left hit] using inv_ne_zero hxi
  · simpa only [laurentInverseCoordinates, ite_eq_right hit] using hxi

end

section

/-! Holomorphic realization of the finite Laurent sectors. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem laurentCoordinateDomain_antitone {s t : Finset ι} (hst : s ⊆ t) :
    laurentCoordinateDomain t ≤ laurentCoordinateDomain s := by
  intro x hx
  exact (mem_laurentCoordinateDomain s x).mpr
    (fun i hi => (mem_laurentCoordinateDomain t x).mp hx i (hst hi))

theorem laurentCoordinateDomain_update {s : Finset ι} {i : ι} (hi : i ∉ s)
    {x : ι → ℂ} (hx : x ∈ laurentCoordinateDomain s) (z : ℂ) :
    Function.update x i z ∈ laurentCoordinateDomain s := by
  apply (mem_laurentCoordinateDomain s _).mpr
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simpa only [Function.update_of_ne hji] using (mem_laurentCoordinateDomain s x).mp hx j hj

theorem laurentInverseCoordinates_differentiableOn (s t : Finset ι) (hts : t ⊆ s) :
    DifferentiableOn ℂ (laurentInverseCoordinates t) (laurentCoordinateDomain s) := by
  apply differentiableOn_pi.mpr
  intro i x hx
  by_cases hi : i ∈ t
  · change DifferentiableWithinAt ℂ (fun x : ι → ℂ => if i ∈ t then (x i)⁻¹ else x i) _ x
    simp only [ite_eq_left hi]
    exact ((differentiableAt_apply (𝕜 := ℂ) i x).fun_inv
      ((mem_laurentCoordinateDomain s x).mp hx i (hts hi))).differentiableWithinAt
  · simpa only [laurentInverseCoordinates, ite_eq_right hi] using
      (differentiableAt_apply (𝕜 := ℂ) i x).differentiableWithinAt

def laurentSectorRealization (s t : Finset ι) (hts : t ⊆ s)
    (a : Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) :
    Holomorphic.FunctionPure.holomorphicFunctions (laurentCoordinateDomain s) :=
  PolynomialHolomorphicSections.AnalyticLocal.functionSectionOfDifferentiable _
    (fun x => a.val ⟨laurentInverseCoordinates t x, trivial⟩)
    (by
      have ha : Differentiable ℂ (FiberVanishing.Dolbeault.holomorphicFunctionExtension ⊤ a) :=
        differentiableOn_univ.mp (FiberVanishing.Dolbeault.holomorphicFunctionExtension_differentiable ⊤ a)
      apply (ha.differentiableOn.comp
        (laurentInverseCoordinates_differentiableOn s t hts) (fun _ _ => Set.mem_univ _)).congr
      intro x _
      exact (Holomorphic.CoefficientMem.openCoefficientExtension_apply ⊤ a.val ⟨laurentInverseCoordinates t x, trivial⟩).symm)

theorem laurentSectorRealization_apply (s t : Finset ι) (hts : t ⊆ s)
    (a : Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) (x : laurentCoordinateDomain s) :
    (laurentSectorRealization s t hts a).val x =
      a.val ⟨laurentInverseCoordinates t x.val, trivial⟩ := rfl

def laurentSectorRealizationMap (s t : Finset ι) (hts : t ⊆ s) :
    Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ)) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (laurentCoordinateDomain s) where
  toFun := laurentSectorRealization s t hts
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def laurentSectorCoefficients (t : Finset ι) :
    Submodule ℂ (Holomorphic.FunctionPure.holomorphicFunctions (⊤ : Opens (ι → ℂ))) where
  carrier := {a | ∀ i ∈ t, ∀ x : (⊤ : Opens (ι → ℂ)), x.val i = 0 → a.val x = 0}
  zero_mem' := by
    intro i hi x hx
    rfl
  add_mem' := by
    intro a b ha hb i hi x hx
    change a.val x + b.val x = 0
    rw [ha i hi x hx, hb i hi x hx, add_zero]
  smul_mem' := by
    intro c a ha i hi x hx
    change c • a.val x = 0
    rw [ha i hi x hx, smul_zero]

end

/-! Uniqueness of the Laurent split on a coordinate puncture domain. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem differentiable_coordinateUpdate (x : ι → ℂ) (i : ι) :
    Differentiable ℂ (fun z : ℂ => Function.update x i z) := by
  apply differentiable_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact differentiable_id
  · simpa only [Function.update_of_ne hji] using (differentiable_const (x j) (𝕜 := ℂ) (E := ℂ))

theorem laurentDomain_slice_differentiable (s : Finset ι) (i : ι) (hi : i ∉ s)
    {f : (ι → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (laurentCoordinateDomain s))
    {x : ι → ℂ} (hx : x ∈ laurentCoordinateDomain s) :
    Differentiable ℂ (fun z : ℂ => f (Function.update x i z)) := by
  intro z
  exact (hf.differentiableAt ((laurentCoordinateDomain s).isOpen.mem_nhds
    (laurentCoordinateDomain_update hi hx z))).comp z (differentiable_coordinateUpdate x i z)

theorem laurentDomain_pair_zero (s : Finset ι) (i : ι) (hi : i ∉ s)
    {a b : (ι → ℂ) → ℂ}
    (ha : DifferentiableOn ℂ a (laurentCoordinateDomain s))
    (hb : DifferentiableOn ℂ b (laurentCoordinateDomain s))
    (hb0 : ∀ x ∈ laurentCoordinateDomain s, x i = 0 → b x = 0)
    (h : ∀ x ∈ laurentCoordinateDomain (insert i s),
      a x + b (Function.update x i (x i)⁻¹) = 0) :
    ∀ x ∈ laurentCoordinateDomain s, a x = 0 ∧ b x = 0 := by
  intro x hx
  have hz : ∀ z ≠ (0 : ℂ),
      a (Function.update x i z) + b (Function.update x i z⁻¹) = 0 := by
    intro z hz
    have hzu : Function.update x i z ∈ laurentCoordinateDomain (insert i s) := by
      apply (mem_laurentCoordinateDomain _ _).mpr
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using hz
      · exact (mem_laurentCoordinateDomain s _).mp (laurentCoordinateDomain_update hi hx z) j hj
    simpa only [Function.update_self, Function.update_idem] using h _ hzu
  have hbz : b (Function.update x i 0) = 0 :=
    hb0 _ (laurentCoordinateDomain_update hi hx 0) (Function.update_self i 0 x)
  obtain ⟨ha', hb'⟩ := ProjectionNaturality.Dolbeault.normalizedLaurent_pair_zero
    (laurentDomain_slice_differentiable s i hi ha hx)
    (laurentDomain_slice_differentiable s i hi hb hx) hbz hz
  exact ⟨by simpa only [Function.update_eq_self] using ha' (x i),
    by simpa only [Function.update_eq_self] using hb' (x i)⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Laurent.SectorTo.Dolbeault
