import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles
import Mathlib.NumberTheory.NumberField.Norm

/-! # Archimedean Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanTrace.CM

noncomputable section

/-! ThetaCycle: the real-linear extension of the actual field trace to
Minkowski space and the archimedean adeles. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

def mixedFieldTrace : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  ∑ i : Module.Free.ChooseBasisIndex ℤ (𝓞 F),
    (Algebra.trace ℚ F (integralBasis F i) : ℝ) • (mixedEmbedding.latticeBasis F).coord i

theorem mixed_field_trace_rational (q : F) :
    mixedFieldTrace F (mixedEmbedding F q) = (Algebra.trace ℚ F q : ℝ) := by
  have ht := congrArg (fun x : ℚ => (x : ℝ))
    (congrArg (Algebra.trace ℚ F) ((integralBasis F).sum_repr q))
  simp only [map_sum, map_smul, smul_eq_mul, Rat.cast_sum, Rat.cast_mul] at ht
  simp only [mixedFieldTrace, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, mixedEmbedding.latticeBasis_repr_apply, smul_eq_mul]
  simpa only [mul_comm] using ht

def infiniteFieldTrace : InfiniteAdeleRing F →+ ℝ :=
  (mixedFieldTrace F).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddMonoidHom

theorem infinite_field_trace_rational (q : F) :
    infiniteFieldTrace F (algebraMap F (InfiniteAdeleRing F) q) = (Algebra.trace ℚ F q : ℝ) := by
  change mixedFieldTrace F (InfiniteAdeleRing.ringEquiv_mixedSpace F
    (algebraMap F (InfiniteAdeleRing F) q)) = _
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact mixed_field_trace_rational F q

theorem infinite_field_trace_continuous : Continuous (infiniteFieldTrace F) :=
  (mixedFieldTrace F).continuous_of_finiteDimensional.comp
    (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous

theorem field_trace_integer (q : 𝓞 F) :
    ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ F (q : F) :=
  ⟨Algebra.trace ℤ (𝓞 F) q, Algebra.coe_trace_int q⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ArchimedeanTrace.CM
