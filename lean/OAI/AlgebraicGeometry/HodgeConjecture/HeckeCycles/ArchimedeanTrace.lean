import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles

/-! # Archimedean Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArchimedeanTrace.CM

noncomputable section

/-! The real-linear extension of the number-field trace to its actual
archimedean adelic space, constructed through the integral basis. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction
variable (F : Type) [Field F] [NumberField F]

def mixedTrace : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  (mixedEmbedding.latticeBasis F).constr ℝ (fun i => (Algebra.trace ℚ F (integralBasis F i) : ℝ))

theorem mixedTrace_continuous : Continuous (mixedTrace F) := (mixedTrace F).continuous_of_finiteDimensional

theorem mixedTrace_rational (x : F) : mixedTrace F (mixedEmbedding F x) = (Algebra.trace ℚ F x : ℝ) := by
  have hx := (integralBasis F).sum_repr x
  have htrace := congrArg (fun y : F => (Algebra.trace ℚ F y : ℝ)) hx
  rw [map_sum] at htrace
  simp only [map_smul, Rat.cast_sum, Rat.cast_mul, smul_eq_mul] at htrace
  rw [mixedTrace, Module.Basis.constr_apply]
  rw [Finsupp.sum_fintype _
    (fun i (a : ℝ) => a • (Algebra.trace ℚ F (integralBasis F i) : ℝ))
    (fun _ => zero_smul ℝ _)]
  simp only [mixedEmbedding.latticeBasis_repr_apply, smul_eq_mul]
  exact htrace

def trace : InfiniteAdeleRing F →+ ℝ :=
  (mixedTrace F).toAddMonoidHom.comp (InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddMonoidHom

theorem trace_continuous : Continuous (CM.trace F) :=
  (mixedTrace_continuous F).comp (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph F).continuous

theorem trace_rational (x : F) : CM.trace F (algebraMap F (InfiniteAdeleRing F) x) = (Algebra.trace ℚ F x : ℝ) := by
  change mixedTrace F (InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) x)) = _
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  exact mixedTrace_rational F x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArchimedeanTrace.CM
