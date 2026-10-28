import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn
import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic

/-! # Split Unitary Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitUnitaryCoordinates.Intrinsic

noncomputable section

/-! The same rational unitary matrix becomes the actual matrices at all
field embeddings after scalar extension. This compares the native rational
action to the coordinates used by the finite local construction. -/

open scoped Classical TensorProduct _root_.Matrix
open OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

def splitUnitaryEnd (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Module.End K ((E →ₐ[ℚ] K) → Fin 3 → K) :=
  LinearMap.pi fun σ => (g.val.val.map σ).mulVecLin.comp (LinearMap.proj σ)

omit [IsGalois ℚ E] [Algebra E K] [IsScalarTower ℚ E K] in
theorem splitUnitaryEnd_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (u : (E →ₐ[ℚ] K) → Fin 3 → K) (σ : E →ₐ[ℚ] K) :
    splitUnitaryEnd E P K g u σ = (g.val.val.map σ).mulVec (u σ) := rfl

theorem splitRankThreeBaseChange_unitary (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (x : K ⊗[ℚ] (Fin 3 → E)) :
    RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange E K ((RationalPhaseColumn.Intrinsic.rationalUnitaryEnd E P g).baseChange K x) =
      splitUnitaryEnd E P K g (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange E K x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange_tmul_eq,
        RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange_tmul_eq, map_smul]
      congr 1
      funext σ i
      exact (RingHom.map_mulVec σ.toRingHom g.val.val x i)

theorem rational_matrix_realizes_split_unitary
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (u : (E →ₐ[ℚ] K) → Fin 3 → K) :
    RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E K e (splitUnitaryEnd E P K g u) =
      (RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E P e g).map (algebraMap ℚ K) *ᵥ RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E K e u := by
  obtain ⟨x, rfl⟩ := (RepresentationTheory.Hecke.RadialDilation.Complexification.Realization.splitRankThreeBaseChange E K).surjective u
  rw [← splitRankThreeBaseChange_unitary]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul, RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates_tmul,
        Matrix.mulVec_smul, RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.rational_matrix_split_mulVec, RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitUnitaryCoordinates.Intrinsic
