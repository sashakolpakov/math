import OAI.RepresentationTheory.Weil.Local.UnitaryInner

/-! # Field Coordinates -/

namespace OAI.RepresentationTheory.Weil.Local.FieldCoordinates.Construction

noncomputable section

section

/-! Transport of the concrete Bruhat space and its energy between topological field presentations. -/

open _root_.MeasureTheory

def fieldPositionEquiv {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) (n : ℕ) :
    FunctionsMetaplectic.Construction.Position k n ≃ₜ+ FunctionsMetaplectic.Construction.Position l n where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := by ext i; exact e.symm_apply_apply (x i)
  right_inv x := by ext i; exact e.apply_symm_apply (x i)
  map_add' x y := by ext i; exact e.map_add (x i) (y i)
  continuous_toFun := continuous_pi (fun i => he.comp (continuous_apply i))
  continuous_invFun := continuous_pi (fun i => he'.comp (continuous_apply i))

theorem schwartzBruhat_comp_crossField
    {k l : Type} [NormedField k] [NormedField l] {m n : ℕ}
    (e : FunctionsMetaplectic.Construction.Position k m ≃ₜ+ FunctionsMetaplectic.Construction.Position l n)
    {f : FunctionsMetaplectic.Construction.Position l n → ℂ} (hf : f ∈ FunctionsMetaplectic.Construction.schwartzBruhat l n) :
    f ∘ e ∈ FunctionsMetaplectic.Construction.schwartzBruhat k m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, a, φ, rfl⟩
      · exact FunctionsMetaplectic.Construction.compact_locallyConstant_mem
          (hf.1.comp_continuous e.continuous) (hf.2.comp_homeomorph e.toHomeomorph)
      · exact FunctionsMetaplectic.Construction.schwartz_coordinate_mem (a.trans e.symm) φ
  | zero => exact (FunctionsMetaplectic.Construction.schwartzBruhat k m).zero_mem
  | add f g _ _ hf hg => exact (FunctionsMetaplectic.Construction.schwartzBruhat k m).add_mem hf hg
  | smul c f _ hf => exact (FunctionsMetaplectic.Construction.schwartzBruhat k m).smul_mem c hf

def testSpaceTransport {k l : Type} [NormedField k] [NormedField l] {m n : ℕ}
    (e : FunctionsMetaplectic.Construction.Position k m ≃ₜ+ FunctionsMetaplectic.Construction.Position l n) : FunctionsMetaplectic.Construction.schwartzBruhat k m ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat l n where
  toFun f := ⟨f.val ∘ e.symm, schwartzBruhat_comp_crossField e.symm f.property⟩
  invFun f := ⟨f.val ∘ e, schwartzBruhat_comp_crossField e f.property⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem testSpaceTransport_apply {k l : Type} [NormedField k] [NormedField l] {m n : ℕ}
    (e : FunctionsMetaplectic.Construction.Position k m ≃ₜ+ FunctionsMetaplectic.Construction.Position l n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k m) (x : FunctionsMetaplectic.Construction.Position l n) :
    (testSpaceTransport e f).val x = f.val (e.symm x) := rfl

theorem testSpaceTransport_energy_congr
    {k l : Type} [NormedField k] [NormedField l] [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    [SecondCountableTopology k] [SecondCountableTopology l] {m n : ℕ}
    (e : FunctionsMetaplectic.Construction.Position k m ≃ₜ+ FunctionsMetaplectic.Construction.Position l n) (f g : FunctionsMetaplectic.Construction.schwartzBruhat k m)
    (hfg : FunctionsMetaplectic.Construction.l2Energy k m f = FunctionsMetaplectic.Construction.l2Energy k m g) :
    FunctionsMetaplectic.Construction.l2Energy l n (testSpaceTransport e f) = FunctionsMetaplectic.Construction.l2Energy l n (testSpaceTransport e g) := by
  let μ := UnitaryInner.Construction.referencePositionMeasure l n
  let ν := UnitaryInner.Construction.referencePositionMeasure k m
  let : (μ.map e.symm).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
  have hμ := Measure.isAddLeftInvariant_eq_smul_of_regular (μ.map e.symm) ν
  have hi (f : FunctionsMetaplectic.Construction.schwartzBruhat k m) : FunctionsMetaplectic.Construction.l2Energy l n (testSpaceTransport e f) =
      (Measure.addHaarScalarFactor (μ.map e.symm) ν : ℝ) * FunctionsMetaplectic.Construction.l2Energy k m f := by
    have h := integral_map_equiv (μ := μ) e.symm.toHomeomorph.toMeasurableEquiv
      (fun x => ‖f.val x‖ ^ 2)
    change (∫ x, ‖f.val x‖ ^ 2 ∂μ.map e.symm) = _ at h
    rw [hμ, integral_smul_nnreal_measure] at h
    exact h.symm
  rw [hi, hi, hfg]

end

section

/-! The actual reference Haar measures under a topological field isomorphism. -/

open _root_.MeasureTheory
open scoped NNReal

def fieldAddHomeomorph {k l : Type} [NormedField k] [NormedField l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) : k ≃ₜ+ l where
  toAddEquiv := e.toAddEquiv
  continuous_toFun := he
  continuous_invFun := he'

def fieldReferenceHaarFactor
    {k l : Type} [NormedField k] [NormedField l]
    [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) : ℝ≥0 :=
  let : ((Measure.addHaar : Measure k).map e).IsAddHaarMeasure :=
    (fieldAddHomeomorph e he he').isAddHaarMeasure_map Measure.addHaar
  Measure.addHaarScalarFactor ((Measure.addHaar : Measure k).map e) (Measure.addHaar : Measure l)

theorem fieldReferenceHaarFactor_pos
    {k l : Type} [NormedField k] [NormedField l]
    [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) :
    0 < fieldReferenceHaarFactor e he he' := by
  let : ((Measure.addHaar : Measure k).map e).IsAddHaarMeasure :=
    (fieldAddHomeomorph e he he').isAddHaarMeasure_map Measure.addHaar
  exact Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

theorem fieldReferenceHaar_map
    {k l : Type} [NormedField k] [NormedField l]
    [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).map e =
      fieldReferenceHaarFactor e he he' • (Measure.addHaar : Measure l) := by
  let : ((Measure.addHaar : Measure k).map e).IsAddHaarMeasure :=
    (fieldAddHomeomorph e he he').isAddHaarMeasure_map Measure.addHaar
  let : ((Measure.addHaar : Measure k).map e).Regular :=
    Measure.Regular.map (fieldAddHomeomorph e he he').toHomeomorph
  exact Measure.isAddLeftInvariant_eq_smul_of_regular _ _

theorem fieldReferenceHaar_integral
    {k l : Type} [NormedField k] [NormedField l]
    [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) (f : k → E) :
    (∫ x, f x ∂Measure.addHaar) =
      (fieldReferenceHaarFactor e he he' : ℝ) • ∫ y, f (e.symm y) ∂Measure.addHaar := by
  have hi := integral_map_equiv (μ := (Measure.addHaar : Measure k))
    (fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y))
  change (∫ y, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldReferenceHaar_map e he he', integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def] using hi.symm

end

/-! The Haar modulus is invariant under a topological field isomorphism. -/

open _root_.MeasureTheory Set
open scoped NNReal ENNReal Pointwise

theorem field_localModulus
    {k l : Type} [NormedField k] [NormedField l]
    [LocallyCompactSpace k] [LocallyCompactSpace l]
    [MeasurableSpace k] [BorelSpace k] [MeasurableSpace l] [BorelSpace l]
    (e : k ≃+* l) (he : Continuous e) (he' : Continuous e.symm) (a : kˣ) :
    FunctionsMetaplectic.Construction.localModulus k a = FunctionsMetaplectic.Construction.localModulus l (Units.map e.toMonoidHom a) := by
  let ν : Measure l := Measure.addHaar
  let μ : Measure k := ν.map e.symm
  let E := fieldAddHomeomorph e he he'
  let : μ.IsAddHaarMeasure := E.symm.isAddHaarMeasure_map ν
  let : μ.Regular := Measure.Regular.map E.symm.toHomeomorph
  let s : Set k := FunctionsMetaplectic.Construction.referenceCompact k
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ
    (FunctionsMetaplectic.Construction.referenceCompact k).interior_nonempty).ne'
  have hsfin : μ s ≠ ⊤ := (FunctionsMetaplectic.Construction.referenceCompact k).isCompact.measure_ne_top
  have hpre : e.symm ⁻¹' (a • s) =
      Units.map e.toMonoidHom a • (e.symm ⁻¹' s) := by
    ext y
    simp only [mem_preimage, mem_smul_set_iff_inv_smul_mem]
    change ((a⁻¹ : kˣ) : k) * e.symm y ∈ s ↔
      e.symm (((Units.map e.toMonoidHom a)⁻¹ : lˣ) * y) ∈ s
    simp only [map_mul, ← map_inv, Units.coe_map]
    change ((a⁻¹ : kˣ) : k) * e.symm y ∈ s ↔
      e.symm (e ((a⁻¹ : kˣ) : k)) * e.symm y ∈ s
    rw [RingEquiv.symm_apply_apply]
  have hmap (t : Set k) : μ t = ν (e.symm ⁻¹' t) :=
    E.symm.toHomeomorph.measurableEmbedding.map_apply ν t
  have hmul : μ (a • s) =
      (distribHaarChar l (Units.map e.toMonoidHom a) : ℝ≥0∞) * μ s := by
    rw [hmap, hmap, hpre]
    exact (distribHaarChar_mul ν (Units.map e.toMonoidHom a) (e.symm ⁻¹' s)).symm
  exact congrArg (fun r : ℝ≥0 => (r : ℝ))
    (distribHaarChar_eq_of_measure_smul_eq_mul hs0 hsfin hmul)

end

end OAI.RepresentationTheory.Weil.Local.FieldCoordinates.Construction
