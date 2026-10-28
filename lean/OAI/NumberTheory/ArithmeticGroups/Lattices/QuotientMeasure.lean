import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Quotient Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction

noncomputable section

section

/-! Quotient compactness and invariant probability measures obtained from
explicit covering sets and finite-measure fundamental domains. -/

open scoped Classical ENNReal
open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem compact_quotient_of_compact_cover
    {H : Type*} [Group H] [TopologicalSpace H] (Γ : Subgroup H)
    (C : Set H) (hC : IsCompact C)
    (hcover : ∀ g : H, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ) :
    CompactSpace (H ⧸ Γ) := by
  have hs : (QuotientGroup.mk : H → H ⧸ Γ) '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨g, rfl⟩ := Quotient.exists_rep z
    obtain ⟨c, hc, γ, hγ, rfl⟩ := hcover g
    refine ⟨c, hc, ?_⟩
    apply QuotientGroup.eq.mpr
    simpa only [inv_mul_cancel_left] using hγ
  exact ⟨hs ▸ hC.image QuotientGroup.continuous_mk⟩

/-- A finite nonzero quotient measure can be normalized while preserving
the action invariance. -/
theorem invariant_probability_of_finite
    {H X : Type*} [Group H] [MulAction H X] [MeasurableSpace X]
    (μ : Measure X) [SMulInvariantMeasure H X μ]
    (hμ0 : μ Set.univ ≠ 0) (hμfin : μ Set.univ ≠ ⊤) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ SMulInvariantMeasure H X ν := by
  refine ⟨(μ Set.univ)⁻¹ • μ, ?_, inferInstance⟩
  constructor
  simp only [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hμ0 hμfin

/-- The measure-theoretic step from a finite Haar fundamental domain to
the lattice definition. The reduction theory must construct the domain. -/
theorem lattice_of_finite_fundamental_domain
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [PolishSpace H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) [DiscreteTopology Γ] [Countable Γ]
    [T2Space (H ⧸ Γ)] [SecondCountableTopology (H ⧸ Γ)]
    (μ : Measure H) [IsMulLeftInvariant μ] [IsMulRightInvariant μ] [SigmaFinite μ]
    (hμ0 : μ ≠ 0) (D : Set H)
    (hD : IsFundamentalDomain Γ.op D μ) (hDfin : μ D < ⊤) :
    IntegralLattice.IsLattice Γ := by
  unfold IntegralLattice.IsLattice
  rw [← (BorelSpace.measurable_eq (α := H ⧸ Γ))]
  let ν : Measure (H ⧸ Γ) := (μ.restrict D).map QuotientGroup.mk
  have hmass : ν Set.univ = μ D := by
    rw [Measure.map_apply QuotientGroup.continuous_mk.measurable MeasurableSet.univ]
    simp
  have hD0 : μ D ≠ 0 := hD.measure_ne_zero hμ0
  let : HasFundamentalDomain Γ.op H μ := hD.hasFundamentalDomain μ
  let : QuotientMeasureEqMeasurePreimage (G := Γ.op) μ ν :=
    hD.quotientMeasureEqMeasurePreimage_quotientMeasure
  let : SMulInvariantMeasure H (H ⧸ Γ) ν :=
    QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient μ
  obtain ⟨η, hηprob, hηinv⟩ := invariant_probability_of_finite (H := H) ν
    (by rwa [hmass]) (by rw [hmass]; exact hDfin.ne)
  exact ⟨inferInstance, η, hηprob, hηinv⟩

end

/-! Transport of coset measures and compactness through continuous group maps. -/

open scoped Classical
open _root_.MeasureTheory _root_.MeasureTheory.Measure

def cosetMap {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) : H ⧸ Γ → K ⧸ Γ.map f :=
  Quotient.map' f fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have hmem : x⁻¹ * y ∈ Γ := QuotientGroup.leftRel_apply.mp hxy
    simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem f hmem

@[simp] theorem cosetMap_mk {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) (x : H) :
    cosetMap f Γ (QuotientGroup.mk x) = QuotientGroup.mk (f x) := rfl

theorem continuous_cosetMap {H K : Type*} [Group H] [Group K]
    [TopologicalSpace H] [TopologicalSpace K]
    (f : H →* K) (hf : Continuous f) (Γ : Subgroup H) :
    Continuous (cosetMap f Γ) := by
  exact hf.quotient_map' _

theorem cosetMap_surjective {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Surjective f) (Γ : Subgroup H) :
    Function.Surjective (cosetMap f Γ) := by
  intro q
  obtain ⟨k, rfl⟩ := Quotient.exists_rep q
  obtain ⟨h, rfl⟩ := hf k
  exact ⟨QuotientGroup.mk h, rfl⟩

theorem cosetMap_smul {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) (h : H) (q : H ⧸ Γ) :
    cosetMap f Γ (h • q) = f h • cosetMap f Γ q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  change QuotientGroup.mk (f (h * x)) = QuotientGroup.mk (f h * f x)
  rw [map_mul]

theorem invariant_measure_map_of_surjective
    {H K X Y : Type*} [Group H] [Group K] [MulAction H X] [MulAction K Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableConstSMul K Y]
    (f : H →* K) (hf : Function.Surjective f) (ψ : X → Y) (hψ : Measurable ψ)
    (hequiv : ∀ h x, ψ (h • x) = f h • ψ x)
    (μ : Measure X) [SMulInvariantMeasure H X μ] :
    SMulInvariantMeasure K Y (μ.map ψ) := by
  constructor
  intro k s hs
  obtain ⟨h, rfl⟩ := hf k
  rw [Measure.map_apply hψ (hs.preimage (measurable_const_smul (f h))),
    Measure.map_apply hψ hs]
  have hpre : ψ ⁻¹' ((f h • ·) ⁻¹' s) = (h • ·) ⁻¹' (ψ ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, hequiv]
  rw [hpre]
  exact SMulInvariantMeasure.measure_preimage_smul h (hs.preimage hψ)

theorem lattice_map_of_surjective
    {H K : Type*} [Group H] [Group K]
    [TopologicalSpace H] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →* K) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup H) (hΓ : IntegralLattice.IsLattice Γ)
    (hdisc : DiscreteTopology (Γ.map f)) : IntegralLattice.IsLattice (Γ.map f) := by
  let : MeasurableSpace (H ⧸ Γ) := borel (H ⧸ Γ)
  let : BorelSpace (H ⧸ Γ) := ⟨rfl⟩
  let : MeasurableSpace (K ⧸ Γ.map f) := borel (K ⧸ Γ.map f)
  let : BorelSpace (K ⧸ Γ.map f) := ⟨rfl⟩
  obtain ⟨_, μ, hμprob, hμinv⟩ := hΓ
  have hmeas : Measurable (cosetMap f Γ) := (continuous_cosetMap f hf Γ).measurable
  refine ⟨hdisc, μ.map (cosetMap f Γ), ?_, ?_⟩
  · exact inferInstance
  · exact invariant_measure_map_of_surjective f hsurj (cosetMap f Γ) hmeas
      (cosetMap_smul f Γ) μ

theorem compact_quotient_map_of_surjective
    {H K : Type*} [Group H] [Group K]
    [TopologicalSpace H] [TopologicalSpace K]
    (f : H →* K) (hf : Continuous f) (hsurj : Function.Surjective f)
    (Γ : Subgroup H) [CompactSpace (H ⧸ Γ)] : CompactSpace (K ⧸ Γ.map f) :=
  Function.Surjective.compactSpace (continuous_cosetMap f hf Γ)
    (cosetMap_surjective f hsurj Γ)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure.Construction
