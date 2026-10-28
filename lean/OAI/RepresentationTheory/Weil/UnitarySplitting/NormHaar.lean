import OAI.RepresentationTheory.Weil.UnitarySplitting.ProperQuadratic
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Norm Haar -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.NormHaar.Construction

noncomputable section

section

/-! Properness of the quadratic field norm and compactness of norm-one fibers. -/

open _root_.Topology

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [FiniteDimensional F E]
variable (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
variable (hQuadratic : Module.finrank F E = 2)

include hF hEmbedding hQuadratic in
theorem quadraticNorm_isProperMap : IsProperMap (Algebra.norm F : E → F) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    let e := QuadraticNorm.Construction.quadraticFieldCoordinates hF hEmbedding hQuadratic
    let q : (Fin 2 → F) → F := fun x => Algebra.norm F (e.symm x)
    have hqc : Continuous q := (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding).comp e.symm.continuous
    have hqh (a : F) (x : Fin 2 → F) : q (a • x) = a ^ 2 * q x := by
      dsimp only [q]
      rw [map_smul, Algebra.smul_def, map_mul, Algebra.norm_algebraMap, hQuadratic]
    have hqz (x : Fin 2 → F) (hx : q x = 0) : x = 0 := by
      have hh : e.symm x = 0 := Algebra.norm_eq_zero_iff.mp hx
      apply e.symm.injective
      simpa using hh
    have hp := ProperQuadratic.Construction.anisotropic_quadratic_isProperMap q hqc hqh hqz
    have hh := hp.comp e.toHomeomorph.isProperMap
    convert hh using 1
    funext x
    change Algebra.norm F x = Algebra.norm F (e.symm (e x))
    rw [e.symm_apply_apply]

include hF hEmbedding hQuadratic in
theorem quadraticNorm_fiber_compact (a : F) : IsCompact {z : E | Algebra.norm F z = a} := by
  exact (quadraticNorm_isProperMap hF hEmbedding hQuadratic).isCompact_preimage isCompact_singleton

include hF hEmbedding hQuadratic in
theorem normOne_compact [CharZero F] (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z) :
    IsCompact {z : E | σ z * z = 1} := by
  have heq : {z : E | σ z * z = 1} = {z : E | Algebra.norm F z = 1} := by
    ext z
    constructor
    · intro hz
      apply (algebraMap F E).injective
      rw [QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne, map_one, mul_comm]
      exact hz
    · intro hz
      have hh := congrArg (algebraMap F E) hz
      rw [QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne, map_one] at hh
      change σ z * z = 1
      rwa [mul_comm]
  rw [heq]
  exact quadraticNorm_fiber_compact hF hEmbedding hQuadratic 1

end

/-! The quadratic norm pushes multiplicative Haar measure to Haar measure
on the norm subgroup specified by the quadratic character. -/

open _root_.Topology _root_.MeasureTheory

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [FiniteDimensional F E]
variable (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))
variable (hQuadratic : Module.finrank F E = 2)

include hF hEmbedding hQuadratic in
theorem normUnits_isProperMap : IsProperMap (Units.map (Algebra.norm F : E →* F)) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨Units.continuous_map (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding), fun K hK => ?_⟩
  apply Units.isEmbedding_val₀.isCompact_iff.mpr
  have heq : ((↑) : Eˣ → E) '' ((Units.map (Algebra.norm F : E →* F)) ⁻¹' K) =
      (Algebra.norm F : E → F) ⁻¹' (((↑) : Fˣ → F) '' K) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨Units.map (Algebra.norm F) u, hu, rfl⟩
    · rintro ⟨v, hv, hxv⟩
      have hNx : Algebra.norm F x ≠ 0 := by rw [← hxv]; exact v.ne_zero
      have hx : x ≠ 0 := Algebra.norm_ne_zero_iff.mp hNx
      refine ⟨Units.mk0 x hx, ?_, rfl⟩
      have he : Units.map (Algebra.norm F) (Units.mk0 x hx) = v := Units.ext hxv.symm
      change Units.map (Algebra.norm F) (Units.mk0 x hx) ∈ K
      rwa [he]
  rw [heq]
  exact (quadraticNorm_isProperMap hF hEmbedding hQuadratic).isCompact_preimage
    (hK.image Units.continuous_val)

variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

def normToKernel : Eˣ →* ω.toMonoidHom.ker :=
  (Units.map (Algebra.norm F : E →* F)).codRestrict ω.toMonoidHom.ker
    (fun b => (hω _).mpr ⟨b, rfl⟩)

omit [CompleteSpace F] [LocallyCompactSpace F] [FiniteDimensional F E] in
theorem normToKernel_surjective : Function.Surjective (normToKernel ω hω) := by
  intro a
  obtain ⟨b, hb⟩ := (hω a.val).mp a.property
  refine ⟨b, Subtype.ext ?_⟩
  exact Units.ext hb

include hF hEmbedding in
omit [LocallyCompactSpace F] in
theorem normToKernel_continuous : Continuous (normToKernel ω hω) :=
  (Units.continuous_map (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding)).subtype_mk _

include hF hEmbedding hQuadratic in
theorem normToKernel_isProperMap : IsProperMap (normToKernel ω hω) := by
  exact isProperMap_of_comp_of_inj
    (normToKernel_continuous hF hEmbedding ω hω) continuous_subtype_val
    (normUnits_isProperMap hF hEmbedding hQuadratic) Subtype.val_injective

include hF hEmbedding hQuadratic in
theorem normToKernel_map_haar
    [MeasurableSpace Eˣ] [BorelSpace Eˣ]
    [MeasurableSpace ω.toMonoidHom.ker] [BorelSpace ω.toMonoidHom.ker]
    (μ : Measure Eˣ) [μ.IsHaarMeasure] :
    (μ.map (normToKernel ω hω)).IsHaarMeasure := by
  exact Measure.isHaarMeasure_map μ (normToKernel ω hω)
    (normToKernel_continuous hF hEmbedding ω hω) (normToKernel_surjective ω hω)
    (by
      rw [Filter.hasBasis_cocompact.tendsto_right_iff]
      intro K hK
      exact (normToKernel_isProperMap hF hEmbedding hQuadratic ω hω).isCompact_preimage hK
        |>.compl_mem_cocompact)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.NormHaar.Construction
