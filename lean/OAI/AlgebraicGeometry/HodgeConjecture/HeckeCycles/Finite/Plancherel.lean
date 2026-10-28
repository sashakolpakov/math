import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg

/-! # Plancherel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Plancherel.CM

noncomputable section

/-! The constructed finite Fourier transform preserves the actual
Haar integral pairing. The proof uses Fourier inversion and the
general vector Fourier adjoint identity over the adelic ring. -/

open scoped Classical InnerProductSpace
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierOperator.CM

def circleCharacter : AddChar RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf Circle where
  toFun a := ⟨Constructed.AdelicCharacter.CM.Finite.character a,
    mem_sphere_zero_iff_norm.mpr (Constructed.AdelicCharacter.CM.Finite.character_unitary a)⟩
  map_zero_eq_one' := Subtype.ext Constructed.AdelicCharacter.CM.Finite.character.map_zero_eq_one
  map_add_eq_mul' a b := Subtype.ext (Constructed.AdelicCharacter.CM.Finite.character.map_add_eq_mul a b)

theorem circleCharacter_continuous : Continuous circleCharacter :=
  Constructed.AdelicCharacter.CM.Finite.character_continuous.subtype_mk _

variable {I : Type*} [Fintype I]

def pairing : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) →ₗ[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := dotProductBilin RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf

theorem pairing_continuous :
    Continuous (fun p : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) => pairing p.1 p.2) :=
  continuous_finsetSum Finset.univ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul
      ((continuous_apply i).comp continuous_snd))

theorem fourier_vector (f : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) f =
      VectorFourier.fourierIntegral circleCharacter (Constructed.FiniteMeasure.CM.measure I) pairing f := by
  funext x
  unfold RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier VectorFourier.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change f y * Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, x i * y i)) =
      Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, y i * x i)) * f y
    simp only [mul_comm]

theorem negative_fourier (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    VectorFourier.fourierIntegral circleCharacter (Constructed.FiniteMeasure.CM.measure I)
      (-pairing.flip) (FourierOperator.CM.fourierMap f).val x = f.val x := by
  have hi := FourierHeisenberg.CM.Inversion.double_fourier f (-x)
  rw [neg_neg] at hi
  rw [← hi, FourierOperator.CM.fourierMap_apply]
  unfold VectorFourier.fourierIntegral RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change Constructed.AdelicCharacter.CM.Finite.character (-(-(∑ i, x i * y i))) * _ =
      _ * Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, (-x) i * y i))
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
    exact mul_comm _ _

theorem unitary (f h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz I) :
    (∫ x, (FourierOperator.CM.fourierMap f).val x * star ((FourierOperator.CM.fourierMap h).val x) ∂(Constructed.FiniteMeasure.CM.measure I)) =
      ∫ x, f.val x * star (h.val x) ∂(Constructed.FiniteMeasure.CM.measure I) := by
  have he := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) (L := pairing) circleCharacter_continuous pairing_continuous
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable h (Constructed.FiniteMeasure.CM.measure I))
    (RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction.finiteSchwartz_integrable (FourierOperator.CM.fourierMap f) (Constructed.FiniteMeasure.CM.measure I))
  rw [← fourier_vector] at he
  simp_rw [negative_fourier] at he
  change (∫ x, inner ℂ ((FourierOperator.CM.fourierMap h).val x) ((FourierOperator.CM.fourierMap f).val x) ∂(Constructed.FiniteMeasure.CM.measure I)) =
    ∫ x, inner ℂ (h.val x) (f.val x) ∂(Constructed.FiniteMeasure.CM.measure I) at he
  simpa only [RCLike.inner_apply, starRingEnd_apply, mul_comm] using he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.Plancherel.CM
