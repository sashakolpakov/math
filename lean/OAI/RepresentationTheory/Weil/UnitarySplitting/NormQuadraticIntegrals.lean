import OAI.RepresentationTheory.Weil.UnitarySplitting.NormAdditiveMeasure

/-! # Norm Quadratic Integrals -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormQuadraticIntegrals.Construction

noncomputable section

section

/-! Integrals over the two fibers of a quadratic character. The vanishing
of the full integral makes the two fiber integrals negatives of each other. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
variable (ω : G →ₜ* Circle) (hsq : ∀ g : G, ω g ^ 2 = 1)

include hsq in
theorem square_one_character_fiber_integral
    (μ : Measure G) (f : G → ℂ) (hf : Integrable f μ) (hzero : ∫ x, f x ∂μ = 0)
    (a : G) :
    (∫ x in {x | ω x = ω a}, f x ∂μ) =
      (ω a : ℂ) * ∫ x in (ω.toMonoidHom.ker : Set G), f x ∂μ := by
  have hval (x : G) : (ω x : ℂ) = 1 ∨ (ω x : ℂ) = -1 :=
    sq_eq_one_iff.mp (congrArg (fun z : Circle => (z : ℂ)) (hsq x))
  by_cases ha : ω a = 1
  · simp only [ha, Circle.coe_one, one_mul]
    rfl
  · have ham : (ω a : ℂ) = -1 := (hval a).resolve_left (fun h => ha (Circle.ext h))
    have hset : {x | ω x = ω a} = (ω.toMonoidHom.ker : Set G)ᶜ := by
      ext x
      change ω x = ω a ↔ ¬ ω x = 1
      constructor
      · intro hx
        rwa [hx]
      · intro hx
        apply Circle.ext
        exact ((hval x).resolve_left (fun h => hx (Circle.ext h))).trans ham.symm
    rw [hset, setIntegral_compl (NormKernelOpen.Construction.square_one_character_kernel_open ω hsq).measurableSet hf,
      hzero, zero_sub, ham, neg_one_mul]

variable [MeasurableMul G]

theorem scaled_measure_character_fiber
    (μ : Measure G) (ρ : G → ℝ≥0)
    (hscale : ∀ a : G, ρ a • μ.map (fun x => a * x) = μ) (a : G) :
    ρ a • (μ.restrict (ω.toMonoidHom.ker : Set G)).map (fun x => a * x) =
      μ.restrict {x | ω x = ω a} := by
  have hfiber : MeasurableSet {x | ω x = ω a} :=
    isClosed_eq ω.continuous continuous_const |>.measurableSet
  have hpre : (fun x => a * x) ⁻¹' {x | ω x = ω a} =
      (ω.toMonoidHom.ker : Set G) := by
    ext x
    change ω (a * x) = ω a ↔ ω x = 1
    rw [map_mul, mul_eq_left]
  have hh := congrArg (fun ν : Measure G => ν.restrict {x | ω x = ω a}) (hscale a)
  rwa [Measure.restrict_smul, Measure.restrict_map (measurable_const_mul a) hfiber, hpre] at hh

include hsq in
theorem scaled_measure_quadratic_character_integral
    (μ : Measure G) (ρ : G → ℝ≥0)
    (hscale : ∀ a : G, ρ a • μ.map (fun x => a * x) = μ)
    (f : G → ℂ) (hfm : StronglyMeasurable f)
    (hf : Integrable f μ) (hzero : ∫ x, f x ∂μ = 0) (a : G) :
    (ρ a : ℂ) * (∫ x in (ω.toMonoidHom.ker : Set G), f (a * x) ∂μ) =
      (ω a : ℂ) * ∫ x in (ω.toMonoidHom.ker : Set G), f x ∂μ := by
  have hh := congrArg (fun ν : Measure G => ∫ x, f x ∂ν)
    (scaled_measure_character_fiber ω μ ρ hscale a)
  rw [integral_smul_nnreal_measure,
    integral_map_of_stronglyMeasurable (measurable_const_mul a) hfm] at hh
  have hi := square_one_character_fiber_integral ω hsq μ f hf hzero a
  exact hh.trans hi

end

section

/-! Quadratic-character scaling of norm integrals against test functions
whose additive integral vanishes. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E]
variable [MeasurableSpace Fˣ] [BorelSpace Fˣ] [MeasurableSpace Eˣ] [BorelSpace Eˣ]
variable [CharZero F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hne hω in
theorem norm_units_integral_scaling
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (f : Fˣ → ℂ) (hfm : StronglyMeasurable f)
    (hf : Integrable f (MultiplicativeHaar.Construction.unitsAdditiveMeasure μF))
    (hzero : ∫ x, f x ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μF = 0) (a : Fˣ) :
    (FieldModulus.Construction.fieldModulus F a : ℂ) *
        (∫ b, f (a * Units.map (Algebra.norm F) b) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μE) =
      (ω a : ℂ) * (∫ b, f (Units.map (Algebra.norm F) b) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μE) := by
  obtain ⟨c, -, hcomp⟩ := NormAdditiveMeasure.Construction.norm_additive_units_measure_comparison
    hF hE hEmbedding hQuadratic σ hne ω hω μF μE
  have hN : Measurable (Units.map (Algebra.norm F : E →* F)) :=
    (Units.continuous_map (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding)).measurable
  have hI (a : Fˣ) :
      (∫ b, f (a * Units.map (Algebra.norm F) b) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μE) =
        (c : ℂ) * ∫ x in (ω.toMonoidHom.ker : Set Fˣ), f (a * x) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μF := by
    have hh := congrArg (fun ν : Measure Fˣ => ∫ x, f (a * x) ∂ν) hcomp
    have hfa : StronglyMeasurable (fun x => f (a * x)) :=
      hfm.comp_measurable (measurable_const_mul a)
    rw [integral_map_of_stronglyMeasurable hN hfa,
      integral_smul_nnreal_measure] at hh
    exact hh
  have hIone := hI 1
  simp only [one_mul] at hIone
  rw [hI, hIone]
  have hchar := scaled_measure_quadratic_character_integral ω
    (Characters.Construction.quadraticCharacter_square hQuadratic ω hω) (MultiplicativeHaar.Construction.unitsAdditiveMeasure μF)
    (FieldModulus.Construction.fieldModulus F) (MultiplicativeHaar.Construction.unitsAdditiveMeasure_scaled μF) f hfm hf hzero a
  calc
    _ = (c : ℂ) * ((FieldModulus.Construction.fieldModulus F a : ℂ) *
        ∫ x in (ω.toMonoidHom.ker : Set Fˣ), f (a * x) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μF) := by ring
    _ = (c : ℂ) * ((ω a : ℂ) *
        ∫ x in (ω.toMonoidHom.ker : Set Fˣ), f x ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μF) := by rw [hchar]
    _ = _ := by ring

end

/-! Field-valued test integrals for the quadratic norm, with the null set
at zero removed only inside the measure-theoretic argument. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

theorem unitsAdditiveMeasure_integral {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (hF : ¬ DiscreteTopology F) (μ : Measure F) [μ.IsAddHaarMeasure] (f : F → ℂ) :
    (∫ u : Fˣ, f (u : F) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μ) = ∫ x, f x ∂μ := by
  rw [← MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.integral_map, NormAdditiveMeasure.Construction.unitsAdditiveMeasure_map_val hF μ]

theorem unitsAdditiveMeasure_integrable {F : Type} [NormedField F] [LocallyCompactSpace F]
    [MeasurableSpace F] [BorelSpace F] [MeasurableSpace Fˣ] [BorelSpace Fˣ]
    (hF : ¬ DiscreteTopology F) (μ : Measure F) [μ.IsAddHaarMeasure] (f : F → ℂ) :
    Integrable (fun u : Fˣ => f (u : F)) (MultiplicativeHaar.Construction.unitsAdditiveMeasure μ) ↔ Integrable f μ := by
  change Integrable (f ∘ ((↑) : Fˣ → F)) (MultiplicativeHaar.Construction.unitsAdditiveMeasure μ) ↔ Integrable f μ
  rw [← MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.integrable_map_iff, NormAdditiveMeasure.Construction.unitsAdditiveMeasure_map_val hF μ]

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [CharZero F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hne hω in
theorem norm_test_integral_scaling
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (f : F → ℂ) (hfm : StronglyMeasurable f) (hf : Integrable f μF)
    (hzero : ∫ x, f x ∂μF = 0) (a : Fˣ) :
    (FieldModulus.Construction.fieldModulus F a : ℂ) * (∫ b, f ((a : F) * Algebra.norm F b) ∂μE) =
      (ω a : ℂ) * (∫ b, f (Algebra.norm F b) ∂μE) := by
  let : MeasurableSpace Fˣ := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let : MeasurableSpace Eˣ := borel Eˣ
  let : BorelSpace Eˣ := ⟨rfl⟩
  have hfm' : StronglyMeasurable (fun u : Fˣ => f (u : F)) :=
    hfm.comp_measurable MultiplicativeHaar.Construction.unitsVal_measurableEmbedding.measurable
  have hf' := (unitsAdditiveMeasure_integrable hF μF f).mpr hf
  have hz : (∫ u : Fˣ, f (u : F) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μF) = 0 := by
    rw [unitsAdditiveMeasure_integral hF μF, hzero]
  have hh := norm_units_integral_scaling hF hE hEmbedding hQuadratic σ hne ω hω
    μF μE (fun u : Fˣ => f (u : F)) hfm' hf' hz a
  change (FieldModulus.Construction.fieldModulus F a : ℂ) *
      (∫ b : Eˣ, f ((a : F) * Algebra.norm F (b : E)) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μE) =
    (ω a : ℂ) * (∫ b : Eˣ, f (Algebra.norm F (b : E)) ∂ MultiplicativeHaar.Construction.unitsAdditiveMeasure μE) at hh
  rw [unitsAdditiveMeasure_integral hE μE (fun b => f ((a : F) * Algebra.norm F b)),
    unitsAdditiveMeasure_integral hE μE (fun b => f (Algebra.norm F b))] at hh
  exact hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormQuadraticIntegrals.Construction
