import OAI.NumberTheory.Quaternion.Arithmetic.CompactQuotientProjection

/-! # Nondiscrete Projection -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.NondiscreteProjection

noncomputable section

/-! A discrete, injective projection would give a quotient slice extending
over the whole omitted factor. Finite invariant volume prevents this when
that factor is noncompact. -/

open scoped Classical Pointwise ENNReal
open Set _root_.MeasureTheory _root_.Topology

theorem open_pos_of_transitive_invariant_probability
    (G X : Type*) [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    [TopologicalSpace X] [LindelofSpace X] [ContinuousConstSMul G X]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ U := by
  have hcover : univ ⊆ ⋃ g : G, g • U := by
    intro x _
    obtain ⟨u, hu⟩ := hne
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G u x
    exact mem_iUnion.mpr ⟨g, smul_mem_smul_set hu⟩
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover
    (fun g : G => g • U) (fun g => hU.smul g) hcover
  apply pos_iff_ne_zero.mpr
  intro hz
  have hz' : μ (⋃ i : ℕ, f i • U) = 0 := by
    apply measure_iUnion_null
    intro i
    rw [measure_smul, hz]
  have := measure_mono_null hf hz'
  simp only [measure_univ, one_ne_zero] at this

variable {L M : Type*} [Group L] [Group M]
  [TopologicalSpace L] [TopologicalSpace M]
  [IsTopologicalGroup L] [IsTopologicalGroup M]

omit [TopologicalSpace L] [IsTopologicalGroup L] in
theorem exists_open_quotient_strip_injOn (Γ : Subgroup (L × M))
    (hinj : Function.Injective ((MonoidHom.snd L M).comp Γ.subtype))
    (hdisc : IsDiscrete (Γ.map (MonoidHom.snd L M) : Set M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧
      InjOn (QuotientGroup.mk : L × M → (L × M) ⧸ Γ) (univ ×ˢ V) := by
  obtain ⟨U, hU, _, hsep⟩ :=
    hdisc.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
  obtain ⟨V, hVU, hV, hV1⟩ := mem_nhds_iff.mp hU
  refine ⟨V, hV, hV1, ?_⟩
  intro x hx y hy hxy
  have hγ : x⁻¹ * y ∈ Γ := QuotientGroup.eq.mp hxy
  have hsecond : x.2⁻¹ * y.2 = 1 := by
    apply hsep _ (Subgroup.mem_map_of_mem (MonoidHom.snd L M) hγ)
    refine ⟨y.2, ⟨x.2, hVU hx.2, ?_⟩, hVU hy.2⟩
    simp
  have hγ1 : (⟨x⁻¹ * y, hγ⟩ : Γ) = 1 := hinj hsecond
  have hval := congrArg Subtype.val hγ1
  exact inv_mul_eq_one.mp hval

def quotientStrip (Γ : Subgroup (L × M)) (V : Set M) (A : Set L) :
    Set ((L × M) ⧸ Γ) := QuotientGroup.mk '' (A ×ˢ V)

theorem quotientStrip_isOpen (Γ : Subgroup (L × M)) {V : Set M} {A : Set L}
    (hV : IsOpen V) (hA : IsOpen A) : IsOpen (quotientStrip Γ V A) :=
  QuotientGroup.isOpenMap_coe _ (hA.prod hV)

omit [TopologicalSpace L] [TopologicalSpace M] [IsTopologicalGroup L] [IsTopologicalGroup M] in
theorem quotientStrip_union (Γ : Subgroup (L × M)) (V : Set M) (A B : Set L) :
    quotientStrip Γ V (A ∪ B) = quotientStrip Γ V A ∪ quotientStrip Γ V B := by
  simp only [quotientStrip, union_prod, image_union]

omit [TopologicalSpace L] [TopologicalSpace M] [IsTopologicalGroup L] [IsTopologicalGroup M] in
theorem quotientStrip_mono (Γ : Subgroup (L × M)) (V : Set M) {A B : Set L}
    (h : A ⊆ B) : quotientStrip Γ V A ⊆ quotientStrip Γ V B :=
  image_mono (prod_mono h Subset.rfl)

omit [TopologicalSpace L] [TopologicalSpace M] [IsTopologicalGroup L] [IsTopologicalGroup M] in
theorem quotientStrip_disjoint (Γ : Subgroup (L × M)) (V : Set M)
    (hinj : InjOn (QuotientGroup.mk : L × M → (L × M) ⧸ Γ) (univ ×ˢ V))
    {A B : Set L} (hAB : Disjoint A B) :
    Disjoint (quotientStrip Γ V A) (quotientStrip Γ V B) := by
  apply disjoint_left.mpr
  rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
  have hab := hinj ⟨mem_univ _, ha.2⟩ ⟨mem_univ _, hb.2⟩ (haz.trans hbz.symm)
  exact (disjoint_left.mp hAB) ha.1 (hab ▸ hb.1)

omit [TopologicalSpace L] [TopologicalSpace M] [IsTopologicalGroup L] [IsTopologicalGroup M] in
theorem quotientStrip_smul (Γ : Subgroup (L × M)) (V : Set M) (A : Set L) (g : L) :
    quotientStrip Γ V (g • A) = (g, (1 : M)) • quotientStrip Γ V A := by
  apply Set.ext
  intro z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨⟨a, ha, rfl⟩, hy⟩, rfl⟩
    refine ⟨QuotientGroup.mk (a, y), ⟨(a, y), ⟨ha, hy⟩, rfl⟩, ?_⟩
    change QuotientGroup.mk ((g, 1) * (a, y)) = QuotientGroup.mk (g * a, y)
    simp
  · rintro ⟨q, ⟨⟨a, y⟩, ⟨ha, hy⟩, rfl⟩, rfl⟩
    refine ⟨(g * a, y), ⟨⟨a, ha, rfl⟩, hy⟩, ?_⟩
    change QuotientGroup.mk (g * a, y) = QuotientGroup.mk ((g, 1) * (a, y))
    simp

/-- Finite invariant quotient volume and an injective projection exclude a
discrete projection when the other factor is noncompact. -/
theorem projected_subgroup_not_discrete
    [LocallyCompactSpace L] [NoncompactSpace L]
    [SecondCountableTopology L] [SecondCountableTopology M]
    (Γ : Subgroup (L × M))
    (hinj : Function.Injective ((MonoidHom.snd L M).comp Γ.subtype))
    (hvolume : CompactQuotientProjection.QuotientHasInvariantProbability Γ) :
    ¬ IsDiscrete (Γ.map (MonoidHom.snd L M) : Set M) := by
  intro hdisc
  obtain ⟨V, hV, hV1, hstrip⟩ := exists_open_quotient_strip_injOn Γ hinj hdisc
  let : MeasurableSpace ((L × M) ⧸ Γ) := borel ((L × M) ⧸ Γ)
  let : BorelSpace ((L × M) ⧸ Γ) := ⟨rfl⟩
  obtain ⟨μ, hprob, hinv⟩ := hvolume
  let : IsProbabilityMeasure μ := hprob
  let : SMulInvariantMeasure (L × M) ((L × M) ⧸ Γ) μ := hinv
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : L)
  let W : Set L := interior K
  have hW : IsOpen W := isOpen_interior
  have hWK : W ⊆ K := interior_subset
  have hW1 : (1 : L) ∈ W := mem_interior_iff_mem_nhds.mpr hK1
  have hpos : 0 < μ (quotientStrip Γ V W) :=
    open_pos_of_transitive_invariant_probability (L × M) ((L × M) ⧸ Γ) μ
      (quotientStrip_isOpen Γ hV hW)
      ⟨QuotientGroup.mk (1, 1), ⟨(1, 1), ⟨hW1, hV1⟩, rfl⟩⟩
  have hgrow : ∀ n : ℕ, ∃ A B : Set L,
      IsOpen A ∧ IsCompact B ∧ A ⊆ B ∧
      n * μ (quotientStrip Γ V W) ≤ μ (quotientStrip Γ V A) := by
    intro n
    induction n with
    | zero =>
      exact ⟨∅, ∅, isOpen_empty, isCompact_empty, Subset.rfl, by simp⟩
    | succ n ih =>
      obtain ⟨A, B, hA, hB, hAB, hmass⟩ := ih
      obtain ⟨g, hg⟩ := exists_disjoint_smul_of_isCompact hB hK
      have hdisj : Disjoint A (g • W) :=
        hg.mono hAB (smul_set_mono hWK)
      refine ⟨A ∪ g • W, B ∪ g • K, hA.union (hW.smul g),
        hB.union (hK.smul g), union_subset_union hAB (smul_set_mono hWK), ?_⟩
      rw [quotientStrip_union, measure_union (quotientStrip_disjoint Γ V hstrip hdisj)
        (quotientStrip_isOpen Γ hV (hW.smul g)).measurableSet,
        quotientStrip_smul, measure_smul, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      exact add_le_add hmass le_rfl
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hpos.ne' (by simp : (1 : ℝ≥0∞) ≠ ∞)
  obtain ⟨A, _, _, _, _, hmass⟩ := hgrow n
  have htotal : μ (quotientStrip Γ V A) ≤ 1 := by
    calc
      _ ≤ μ univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
  exact (not_lt_of_ge (hmass.trans htotal)) hn

end

end OAI.NumberTheory.Quaternion.Arithmetic.NondiscreteProjection
