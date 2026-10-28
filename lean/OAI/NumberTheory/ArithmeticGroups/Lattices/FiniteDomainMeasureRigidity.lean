import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure

/-! # Finite Domain Measure Rigidity -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity.Construction

noncomputable section

section

/-! Measurable fundamental domains selected inside an orbit-covering set.
The construction takes the first member of a countable family of local slices
that an orbit meets. -/

open scoped Classical
open Set _root_.MeasureTheory _root_.MeasureTheory.Measure

section Selection
variable {G X : Type*} [Group G] [MulAction G X]

def firstOrbitSlice (U : ℕ → Set X) (n : ℕ) : Set X :=
  U n \ ⋃ (j : ℕ) (_ : j < n) (g : G), (g • ·) ⁻¹' U j

theorem mem_firstOrbitSlice (U : ℕ → Set X) (n : ℕ) (x : X) :
    x ∈ firstOrbitSlice (G := G) U n ↔
      x ∈ U n ∧ ∀ j < n, ∀ g : G, g • x ∉ U j := by
  simp [firstOrbitSlice]

theorem firstOrbitSlice_measurable [Countable G] [MeasurableSpace X]
    [MeasurableConstSMul G X] (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (n : ℕ) : MeasurableSet (firstOrbitSlice (G := G) U n) := by
  exact (hU n).diff (MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun g =>
      (hU j).preimage (measurable_const_smul g))

theorem firstOrbitSlice_unique
    (U : ℕ → Set X)
    (hU : ∀ n x (g h : G), g • x ∈ U n → h • x ∈ U n → g = h)
    (x : X) {g h : G} {i j : ℕ}
    (hg : g • x ∈ firstOrbitSlice (G := G) U i)
    (hh : h • x ∈ firstOrbitSlice (G := G) U j) : g = h := by
  rw [mem_firstOrbitSlice] at hg hh
  have hij : i = j := by
    apply le_antisymm
    · by_contra hn
      exact hg.2 j (Nat.lt_of_not_ge hn) (h * g⁻¹)
        (by simpa [mul_smul] using hh.1)
    · by_contra hn
      exact hh.2 i (Nat.lt_of_not_ge hn) (g * h⁻¹)
        (by simpa [mul_smul] using hg.1)
  exact hU i x g h hg.1 (hij ▸ hh.1)

theorem exists_firstOrbitSlice
    (U : ℕ → Set X) (x : X) (hx : ∃ n, ∃ g : G, g • x ∈ U n) :
    ∃ n, ∃ g : G, g • x ∈ firstOrbitSlice (G := G) U n := by
  obtain ⟨g, hg⟩ := Nat.find_spec hx
  refine ⟨Nat.find hx, g, (mem_firstOrbitSlice _ _ _).mpr ⟨hg, ?_⟩⟩
  intro j hj h hh
  exact Nat.find_min hx hj ⟨h * g, by simpa [mul_smul] using hh⟩

theorem fundamentalDomain_of_countable_slices
    [Countable G] [MeasurableSpace X] [MeasurableConstSMul G X]
    (μ : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hinj : ∀ n x (g h : G), g • x ∈ U n → h • x ∈ U n → g = h)
    (hcover : ∀ x, ∃ n, ∃ g : G, g • x ∈ U n) :
    IsFundamentalDomain G (⋃ n, firstOrbitSlice (G := G) U n) μ := by
  apply IsFundamentalDomain.mk'
  · exact (MeasurableSet.iUnion (firstOrbitSlice_measurable U hU)).nullMeasurableSet
  intro x
  obtain ⟨n, g, hg⟩ := exists_firstOrbitSlice U x (hcover x)
  refine ⟨g, mem_iUnion.mpr ⟨n, hg⟩, ?_⟩
  intro h hh
  obtain ⟨m, hm⟩ := mem_iUnion.mp hh
  exact firstOrbitSlice_unique U hinj x hm hg

theorem exists_fundamentalDomain_subset_of_slices
    [Countable G] [MeasurableSpace X] [MeasurableConstSMul G X]
    (μ : Measure X) (D : Set X) (hD : MeasurableSet D)
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hinj : ∀ n x (g h : G), g • x ∈ U n → h • x ∈ U n → g = h)
    (hcover : ∀ x, ∃ n, x ∈ U n)
    (hDcover : ∀ x, ∃ g : G, g • x ∈ D) :
    ∃ F ⊆ D, MeasurableSet F ∧ IsFundamentalDomain G F μ := by
  let V : ℕ → Set X := fun n => D ∩ U n
  have hV : ∀ n, MeasurableSet (V n) := fun n => hD.inter (hU n)
  refine ⟨⋃ n, firstOrbitSlice (G := G) V n, ?_,
    MeasurableSet.iUnion (firstOrbitSlice_measurable V hV), ?_⟩
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact ((mem_firstOrbitSlice V n x).mp hn).1.1
  apply fundamentalDomain_of_countable_slices μ V hV
  · exact fun n x g h hg hh => hinj n x g h hg.2 hh.2
  intro x
  obtain ⟨g, hg⟩ := hDcover x
  obtain ⟨n, hn⟩ := hcover (g • x)
  exact ⟨n, g, hg, hn⟩

end Selection

theorem exists_countable_slices_of_quotientCovering
    {G X Y : Type*} [Group G] [MulAction G X]
    [TopologicalSpace X] [TopologicalSpace Y]
    [SecondCountableTopology X] [Nonempty X]
    {f : X → Y} (hf : IsQuotientCoveringMap f G) :
    ∃ U : ℕ → Set X, (∀ n, IsOpen (U n)) ∧
      (∀ n x (g h : G), g • x ∈ U n → h • x ∈ U n → g = h) ∧
      (∀ x, ∃ n, x ∈ U n) := by
  have hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
    intro x
    obtain ⟨V, hV, hd⟩ := hf.disjoint x
    obtain ⟨U, hUV, hU, hx⟩ := mem_nhds_iff.mp hV
    refine ⟨U, hU, hx, fun g hg => hd g ?_⟩
    obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hg
    exact ⟨g • z, ⟨z, hUV hz, rfl⟩, hUV hy⟩
  choose U hU hx hd using hlocal
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨fun n => U (a n), fun n => hU (a n), ?_, ?_⟩
  · intro n x g h hg hh
    have he : h * g⁻¹ = 1 := hd (a n) (h * g⁻¹)
      ⟨h • x, ⟨g • x, hg, by simp [mul_smul]⟩, hh⟩
    exact (mul_inv_eq_one.mp he).symm
  · intro x
    exact mem_iUnion.mp (ha (mem_univ x))

theorem exists_fundamentalDomain_subset_of_discrete
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [Countable Γ]
    (μ : Measure H) (D : Set H) (hD : MeasurableSet D)
    (hcover : ∀ x : H, ∃ g : Γ.op, g • x ∈ D) :
    ∃ F ⊆ D, MeasurableSet F ∧ IsFundamentalDomain Γ.op F μ := by
  have hf : IsQuotientCoveringMap (QuotientGroup.mk : H → H ⧸ Γ) Γ.op :=
    isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroupOp Γ
      (isDiscrete_iff_discreteTopology.mpr inferInstance) QuotientGroup.eq
  obtain ⟨U, hU, hinj, hUc⟩ := exists_countable_slices_of_quotientCovering hf
  exact exists_fundamentalDomain_subset_of_slices μ D hD U
    (fun n => (hU n).measurableSet) hinj hUc hcover

theorem lattice_of_finite_cover
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [Countable Γ]
    [T2Space (H ⧸ Γ)] [SecondCountableTopology (H ⧸ Γ)]
    (μ : Measure H) [IsMulLeftInvariant μ] [IsMulRightInvariant μ] [SigmaFinite μ]
    (hμ0 : μ ≠ 0) (D : Set H) (hD : MeasurableSet D) (hDfin : μ D < ⊤)
    (hcover : ∀ x : H, ∃ c ∈ D, ∃ γ ∈ Γ, x = c * γ) :
    IntegralLattice.IsLattice Γ := by
  obtain ⟨F, hFD, _, hF⟩ := exists_fundamentalDomain_subset_of_discrete Γ μ D hD
    (fun x => by
      obtain ⟨c, hc, γ, hγ, rfl⟩ := hcover x
      refine ⟨⟨MulOpposite.op γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
      simpa using hc)
  exact QuotientMeasure.Construction.lattice_of_finite_fundamental_domain Γ μ hμ0 F hF
    ((measure_mono hFD).trans_lt hDfin)

end

/-! A scalar change of measure commuting with a countable group action
must be trivial when the action has a fundamental domain of positive
finite measure. -/

open scoped Classical ENNReal
open Set _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem measurePreserving_of_scalar_and_finite_fundamentalDomain
    {Γ X : Type*} [Group Γ] [Countable Γ] [MulAction Γ X]
    [MeasurableSpace X] [MeasurableConstSMul Γ X]
    (μ : Measure X) [SMulInvariantMeasure Γ X μ] (hμ0 : μ ≠ 0)
    (F : Set X) (hFmeas : MeasurableSet F) (hF : IsFundamentalDomain Γ F μ)
    (hFfin : μ F < ⊤) (f : X → X) (hf : Measurable f)
    (hcomm : ∀ (g : Γ) (x : X), f (g • x) = g • f x)
    (c : ℝ≥0∞) (hc : μ.map f = c • μ) : MeasurePreserving f μ μ := by
  have hqmp : QuasiMeasurePreserving f μ μ := ⟨hf, by rw [hc]; exact smul_absolutelyContinuous⟩
  have hpre : IsFundamentalDomain Γ (f ⁻¹' F) μ :=
    hF.preimage_of_equiv hqmp Function.bijective_id (fun g x => hcomm g x)
  have hmass : c * μ F = μ F := by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← hc, Measure.map_apply hf hFmeas]
    exact (hF.measure_eq hpre).symm
  have hc1 : c = 1 := (ENNReal.mul_eq_right (hF.measure_ne_zero hμ0) hFfin.ne).mp hmass
  exact ⟨hf, by rw [hc, hc1, one_smul]⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.FiniteDomainMeasureRigidity.Construction
