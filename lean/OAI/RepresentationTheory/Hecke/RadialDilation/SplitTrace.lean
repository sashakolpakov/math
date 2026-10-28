import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticBasis
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Split Trace -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization

noncomputable section

/-! The rational trace pairing in split embedding coordinates. -/

open scoped Classical TensorProduct _root_.Matrix

theorem trace_eq_sum_split_embeddings
    (E K : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K] (x : E) :
    algebraMap ℚ K (Algebra.trace ℚ E x) = ∑ σ : E →ₐ[ℚ] K, σ x := by
  calc
    _ = ∑ τ : Gal(E/ℚ), algebraMap E K (τ x) := by
      rw [IsScalarTower.algebraMap_apply ℚ E K, trace_eq_sum_automorphisms, map_sum]
    _ = _ := by
      calc
        _ = ∑ τ : Gal(E/ℚ), ((Normal.algHomEquivAut ℚ K E).symm τ) x := by
          apply Finset.sum_congr rfl
          intro τ _
          rfl
        _ = _ := (Normal.algHomEquivAut ℚ K E).symm.sum_comp (fun σ : E →ₐ[ℚ] K => σ x)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

def conjugateSplitEmbedding (σ : E →ₐ[ℚ] K) : E →ₐ[ℚ] K :=
  σ.comp (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E).toAlgHom

def splitTraceBilinear (θ : E) (H : Matrix (Fin 3) (Fin 3) E) :
    LinearMap.BilinForm K ((E →ₐ[ℚ] K) → Fin 3 → K) :=
  ∑ σ : E →ₐ[ℚ] K, σ θ •
    (Matrix.toBilin' (H.map σ)).compl₁₂ (LinearMap.proj σ) (LinearMap.proj (conjugateSplitEmbedding E K σ))

omit [IsGalois ℚ E] [Algebra E K] [IsScalarTower ℚ E K] in
theorem splitTraceBilinear_apply (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (u v : (E →ₐ[ℚ] K) → Fin 3 → K) :
    splitTraceBilinear E K θ H u v =
      ∑ σ : E →ₐ[ℚ] K, σ θ * ∑ j, ∑ k, u σ j * σ (H j k) * v (conjugateSplitEmbedding E K σ) k := by
  simp [splitTraceBilinear, Matrix.toBilin'_apply, Finset.mul_sum, mul_assoc]

theorem splitTraceBilinear_rational (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → E) :
    splitTraceBilinear E K θ H (fun σ i => σ (x i)) (fun σ i => σ (y i)) =
      algebraMap ℚ K (SymplecticBasis.Realization.rationalTraceForm E θ H x y) := by
  rw [splitTraceBilinear_apply, SymplecticBasis.Realization.rationalTraceForm_apply, trace_eq_sum_split_embeddings E K]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [conjugateSplitEmbedding, AlgHom.comp_apply, AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation,
    AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply, map_mul, map_sum]

theorem splitTraceBilinear_baseChange (θ : E) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : K ⊗[ℚ] (Fin 3 → E)) :
    splitTraceBilinear E K θ H (Complexification.Realization.splitRankThreeBaseChange E K x) (Complexification.Realization.splitRankThreeBaseChange E K y) =
      (SymplecticBasis.Realization.rationalTraceForm E θ H).baseChange K x y := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      | tmul b y =>
          rw [Complexification.Realization.splitRankThreeBaseChange_tmul_eq, Complexification.Realization.splitRankThreeBaseChange_tmul_eq]
          rw [LinearMap.map_smul₂, map_smul, splitTraceBilinear_rational,
            LinearMap.BilinForm.baseChange_tmul]
          simp only [smul_eq_mul, Algebra.smul_def]
          ring

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization
