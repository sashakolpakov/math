import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTestCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteCharacter
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.AdelicCharacter

/-! # Adelic Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTrace.CM

noncomputable section

/-! The actual field trace extends continuously to finite adeles. The
constructed number-field character is the rational character of this trace. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

def coordinates (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf :=
  fun i => CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicLinearEquiv F Unit (fun _ => a) ((), i)

theorem coordinates_rational (a : F) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 F)) :
    coordinates F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) i =
      algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf ((integralBasis F).repr a i) :=
  congrFun (CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicLinearEquiv_rational F Unit (fun _ => a)) ((), i)

def trace : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F →ₗ[ℚ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf where
  toFun a := ∑ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (Algebra.trace ℚ F (integralBasis F i)) * coordinates F a i
  map_add' a b := by
    simp only [coordinates, show (fun _ : Unit => a + b) = (fun _ => a) + (fun _ => b) from rfl,
      map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [coordinates, show (fun _ : Unit => c • a) = c • (fun _ => a) from rfl,
      map_smul, Pi.smul_apply, RingHom.id_apply, mul_smul_comm, Finset.smul_sum]

theorem trace_continuous : Continuous (CM.trace F) := by
  apply continuous_finsetSum Finset.univ
  intro i _
  exact continuous_const.mul ((continuous_apply ((), i)).comp
    ((CMExtraction.IntegralAdelicCoordinates.TestTransport.integralAdelicLinearEquiv F Unit).continuous.comp (continuous_pi fun _ => continuous_id)))

theorem trace_rational (a : F) :
    CM.trace F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) = algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (Algebra.trace ℚ F a) := by
  change (∑ i, algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf (Algebra.trace ℚ F (integralBasis F i)) *
    coordinates F (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) a) i) = _
  simp only [coordinates_rational, ← map_mul, ← map_sum]
  apply congrArg (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
  have h := congrArg (Algebra.trace ℚ F) ((integralBasis F).sum_repr a)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem character_trace (a : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :
    Constructed.AdelicCharacter.CM.Finite.character (CM.trace F a) =
      HeckeCycles.NumberField.FiniteCharacter.CM.character F a := by
  have he : (fun x => Constructed.AdelicCharacter.CM.Finite.character (CM.trace F x)) =
      (fun x => HeckeCycles.NumberField.FiniteCharacter.CM.character F x) := by
    apply (RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).equalizer
      (Constructed.AdelicCharacter.CM.Finite.character_continuous.comp (trace_continuous F))
      (HeckeCycles.NumberField.FiniteCharacter.CM.character_continuous F)
    funext x
    dsimp only [Function.comp_apply]
    rw [trace_rational, Constructed.AdelicCharacter.CM.Finite.character_rational,
      HeckeCycles.NumberField.FiniteCharacter.CM.character_rational]
  exact congrFun he a

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.AdelicTrace.CM
