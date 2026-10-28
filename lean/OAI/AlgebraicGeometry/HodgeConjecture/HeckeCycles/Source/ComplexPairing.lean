import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameBilinearExt
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.RingSymplecticPairing

/-! # Complex Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexPairing.CM

noncomputable section

/-! Extend the source's specified rational symplectic identity to its
actual complex CM components. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def coordinate (τ : Gal(E/ℚ)) (i : Fin 3) : GeometricSource.CM.Ambient E →ₗ[ℂ] ℂ :=
  (LinearMap.proj i : GeometricSource.CM.Vec ℂ →ₗ[ℂ] ℂ).comp (LinearMap.proj τ : GeometricSource.CM.Ambient E →ₗ[ℂ] GeometricSource.CM.Vec ℂ)

def ambientForm (b δ a : E) : LinearMap.BilinForm ℂ (GeometricSource.CM.Ambient E) :=
  ∑ τ : Gal(E/ℚ), ∑ i : Fin 3,
    (((τ (δ * a) : E) : ℂ) * (if i = 2 then ((τ b : E) : ℂ) else 1)) •
      (LinearMap.mul ℂ ℂ).compl₁₂ (coordinate E τ i) (coordinate E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i)

theorem ambientForm_apply (b δ a : E) (x y : GeometricSource.CM.Ambient E) :
    ambientForm E b δ a x y = ∑ τ : Gal(E/ℚ), ∑ i : Fin 3,
      (((τ (δ * a) : E) : ℂ) * (if i = 2 then ((τ b : E) : ℂ) else 1)) *
        (x τ i * y (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i) := by
  simp only [ambientForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.compl₁₂_apply, coordinate, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.mul_apply']

variable [IsGalois ℚ E]

omit [NumberField.IsCMField E] in
theorem trace_sum (z : E) : (Algebra.trace ℚ E z : ℂ) = ∑ τ : Gal(E/ℚ), ((τ z : E) : ℂ) := by
  have h := congrArg (fun z : E => (z : ℂ)) (trace_eq_sum_automorphisms (K := ℚ) z)
  simpa using h

theorem ambient_rational (b δ a : E) (x y : GeometricSource.CM.Vec E) :
    ambientForm E b δ a (GeometricSource.CM.embeddingCoordinates E x) (GeometricSource.CM.embeddingCoordinates E y) =
      (Algebra.trace ℚ E (δ * a * GeometricSource.CM.hermitian E b x y) : ℂ) := by
  rw [ambientForm_apply, trace_sum]
  apply Finset.sum_congr rfl
  intro τ _
  have hc (z : E) : τ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E z) = (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) z :=
    congrArg (fun σ : Gal(E/ℚ) => σ z) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ).eq.symm
  simp only [GeometricSource.CM.hermitian, map_mul, map_sum, apply_ite τ, map_one, hc,
    IntermediateField.coe_mul, IntermediateField.coe_sum, GeometricSource.CM.embeddingCoordinates,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · ring
  · simp only [IntermediateField.coe_one]
    ring

variable {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} (C : GeometricSource.CM.SymplecticCoordinates E B places)

def frameForm : LinearMap.BilinForm ℂ (GeometricSource.CM.Ambient E) :=
  (-(Matrix.J (GeometricSource.CM.Positions E places) ℂ).toBilin').compl₁₂
    (ComplexAction.CM.complexFrame E C).toLinearMap (ComplexAction.CM.complexFrame E C).toLinearMap

omit [IsGalois ℚ E] in
theorem frameForm_apply (x y : GeometricSource.CM.Ambient E) :
    frameForm E C x y =
      Finite.TracePhase.CM.pairing (ComplexAction.CM.complexFrame E C x) (ComplexAction.CM.complexFrame E C y) :=
  (RingSymplecticPairing.CM.pairing_negJ _ _).symm

omit [IsGalois ℚ E] in
theorem frame_rational (x y : GeometricSource.CM.Vec E) :
    frameForm E C (GeometricSource.CM.embeddingCoordinates E x) (GeometricSource.CM.embeddingCoordinates E y) =
      (Algebra.trace ℚ E (C.delta * C.a * GeometricSource.CM.hermitian E B.b x y) : ℂ) := by
  rw [frameForm_apply, ComplexAction.CM.complexFrame_rational, ComplexAction.CM.complexFrame_rational]
  have h := congrArg (fun t : ℚ => (t : ℂ)) (ComplexAction.CM.Symplectic.frame_pairing E C x y)
  simpa only [Finite.TracePhase.CM.pairing, ComplexAction.CM.Symplectic.pairing, Rat.cast_sum, Rat.cast_sub, Rat.cast_mul,
    mul_comm] using h

theorem form_equality : frameForm E C = ambientForm E B.b C.delta C.a := by
  apply Rational.FrameBilinearExt.CM.ext (ComplexAction.CM.Symplectic.frame E C) (ComplexAction.CM.complexFrame E C)
    (GeometricSource.CM.embeddingCoordinates E) (ComplexAction.CM.complexFrame_rational E C)
  intro x y
  exact (frame_rational E C x y).trans (ambient_rational E B.b C.delta C.a x y).symm

theorem pairing (x y : GeometricSource.CM.Ambient E) :
    Finite.TracePhase.CM.pairing (ComplexAction.CM.complexFrame E C x) (ComplexAction.CM.complexFrame E C y) =
      ∑ τ : Gal(E/ℚ), ∑ i : Fin 3,
        (((τ (C.delta * C.a) : E) : ℂ) * (if i = 2 then ((τ B.b : E) : ℂ) else 1)) *
          (x τ i * y (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) i) := by
  rw [← frameForm_apply, form_equality, ambientForm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexPairing.CM
