import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Integrability
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Real.Fourier
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FourierHeisenberg
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ProductOperators

/-! # Fourier -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier.CM

noncomputable section

/-! The actual adelic Fourier automorphism and its integral formula,
constructed independently of rational splitting or Weil data. -/

open scoped Classical
open _root_.MeasureTheory
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.FiniteMeasure.CM
variable {I : Type*} [Fintype I]

theorem adelic_fourier_tensor_function (f : (I → ℝ) → ℂ) (φ : (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) → ℂ)
    (x : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure I))
      (fun y => f (fun i => (y i).1) * φ (fun i => (y i).2)) x =
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter volume f (fun i => (x i).1) *
          RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.Finite.character (Constructed.FiniteMeasure.CM.measure I) φ (fun i => (x i).2) := by
  change (∫ y, (f (fun i => (y i).1) * φ (fun i => (y i).2)) *
    Constructed.AdelicCharacter.CM.character (-(∑ i, x i * y i)) ∂Measure.map RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv (volume.prod (Constructed.FiniteMeasure.CM.measure I))) = _
  rw [RepresentationTheory.Theta.AdelicTopology.PoissonAutomorphyConstruction.adelicProductEquiv.measurableEmbedding.integral_map]
  calc
    _ = ∫ y : (I → ℝ) × (I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf),
        (f y.1 * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, (x i).1 * y.1 i))) *
          (φ y.2 * Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, (x i).2 * y.2 i))) ∂volume.prod (Constructed.FiniteMeasure.CM.measure I) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (f y.1 * φ y.2) * Constructed.AdelicCharacter.CM.character (-(∑ i, x i * (y.1 i, y.2 i))) = _
        have heq : -(∑ i, x i * (y.1 i, y.2 i)) =
            (-(∑ i, (x i).1 * y.1 i), -(∑ i, (x i).2 * y.2 i)) := by
          apply Prod.ext
          · change -((RingHom.fst ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (∑ i, x i * (y.1 i, y.2 i))) = _
            rw [map_sum]
            rfl
          · change -((RingHom.snd ℝ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (∑ i, x i * (y.1 i, y.2 i))) = _
            rw [map_sum]
            rfl
        rw [heq, Constructed.AdelicCharacter.CM.character_apply]
        ring
    _ = _ := by
      simpa only [RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier] using! integral_prod_mul (μ := volume) (ν := (Constructed.FiniteMeasure.CM.measure I))
        (fun y : I → ℝ => f y * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.standardRealCharacter (-(∑ i, (x i).1 * y i)))
        (fun y : I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => φ y * Constructed.AdelicCharacter.CM.Finite.character (-(∑ i, (x i).2 * y i)))

def raw : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz I →ₗ[ℂ] ((I → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) → ℂ) where
  toFun F := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.character (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure I)) F.val
  map_add' F G := by
    funext x
    change (∫ y, (F.val y + G.val y) * Constructed.AdelicCharacter.CM.character (-(∑ i, x i * y i))
      ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure I)) = _
    simp only [add_mul]
    exact integral_add (Integrability.CM.fourier_integrable (Constructed.FiniteMeasure.CM.measure I) F x)
      (Integrability.CM.fourier_integrable (Constructed.FiniteMeasure.CM.measure I) G x)
  map_smul' c F := by
    funext x
    change (∫ y, (c * F.val y) * Constructed.AdelicCharacter.CM.character (-(∑ i, x i * y i))
      ∂ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure I)) = _
    simp only [mul_assoc]
    exact integral_const_mul _ _

def fourierEquiv (n : ℕ) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n) :=
  ProductOperators.CM.operator
    (Real.Fourier.CM.fourierEquiv n, Finite.FourierHeisenberg.CM.Equiv.fourierEquiv (I := Fin n))

theorem fourierEquiv_tensor (n : ℕ) (f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realSchwartz (Fin n)) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) :
    fourierEquiv n (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor (Real.Fourier.CM.fourierEquiv n f)
      (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv φ) :=
  ProductOperators.CM.operator_tensor _ _ f φ

theorem fourierEquiv_raw (n : ℕ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)).subtype.comp (fourierEquiv n).toLinearMap = raw := by
  apply FiniteOperators.CM.Sections.linear_ext
  intro f φ
  change (fourierEquiv n (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)).val = raw (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.tensor f φ)
  rw [fourierEquiv_tensor]
  funext x
  change (Real.Fourier.CM.fourierEquiv n f).val (fun i => (x i).1) *
    (Finite.FourierHeisenberg.CM.Equiv.fourierEquiv φ).val (fun i => (x i).2) = _
  rw [Real.Fourier.CM.fourierEquiv_apply, Finite.FourierHeisenberg.CM.Equiv.fourierEquiv_apply]
  exact (adelic_fourier_tensor_function f.val φ.val x).symm

theorem fourierEquiv_apply (n : ℕ) (F : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz (Fin n)) (x : Fin n → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQ) :
    (fourierEquiv n F).val x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.fourier Constructed.AdelicCharacter.CM.character
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicMeasure (Constructed.FiniteMeasure.CM.measure (Fin n))) F.val x :=
  congrFun (LinearMap.congr_fun (fourierEquiv_raw n) F) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.Fourier.CM
