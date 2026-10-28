import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitUnitaryCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryCrossMatrix

/-! # Local Unitary Phase -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitaryPhase.Intrinsic

noncomputable section

/-! The native symplectic coordinate change sends every rational SU
matrix to its actual local blocks and their inverse transposes. -/

open scoped Classical TensorProduct _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]
  (σ : Fin s → E →ₐ[ℚ] K) (hσ : Function.Bijective (RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace.Realization.splitPairingEmbeddings E K σ))
  (θ : E) (hθ : θ ≠ 0) (hH : (Intrinsic.Multiplicity.nativeMatrix E P).det ≠ 0)

def localUnitaryPhase (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (x : Sum (Fin s × Fin 3) (Fin s × Fin 3) → K) :
    Sum (Fin s × Fin 3) (Fin s × Fin 3) → K :=
  Sum.elim
    (fun p => ((g.val.val.map (σ p.1)) *ᵥ (fun i => x (Sum.inl (p.1, i)))) p.2)
    (fun p => (((Matrix.SpecialLinearGroup.map (σ p.1).toRingHom g.val)⁻¹).val.transpose *ᵥ
      (fun i => x (Sum.inr (p.1, i)))) p.2)

omit [IsGalois ℚ E] [Algebra E K] [IsScalarTower ℚ E K] in
theorem splitSymplecticCoordinates_unitary (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (u : (E →ₐ[ℚ] K) → Fin 3 → K) :
    RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ (Intrinsic.Multiplicity.nativeMatrix E P) hH (SplitUnitaryCoordinates.Intrinsic.splitUnitaryEnd E P K g u) =
      localUnitaryPhase E P K σ g (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.splitSymplecticCoordinates E K σ hσ θ hθ (Intrinsic.Multiplicity.nativeMatrix E P) hH u) := by
  funext i
  cases i with
  | inl p => rfl
  | inr p =>
      change ((σ p.1 θ • (Intrinsic.Multiplicity.nativeMatrix E P).map (σ p.1)) *ᵥ
          ((g.val.val.map (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K (σ p.1))) *ᵥ
            u (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K (σ p.1)))) p.2 =
        (((Matrix.SpecialLinearGroup.map (σ p.1).toRingHom g.val)⁻¹).val.transpose *ᵥ
          ((σ p.1 θ • (Intrinsic.Multiplicity.nativeMatrix E P).map (σ p.1)) *ᵥ
            u (RepresentationTheory.Hecke.RadialDilation.SplitTrace.Realization.conjugateSplitEmbedding E K (σ p.1)))) p.2
      rw [Matrix.mulVec_mulVec, UnitaryCrossMatrix.Intrinsic.unitary_cross_inverseTranspose, Matrix.mulVec_mulVec]

theorem rationalToSplitCoordinates_unitary
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (x : Sum (Fin s × Fin 3) (Fin s × Fin 3) → K) :
    RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates E K σ hσ θ hθ (Intrinsic.Multiplicity.nativeMatrix E P) hH e
      ((RationalPhaseColumn.Intrinsic.rationalUnitaryMatrix E P e g).map (algebraMap ℚ K) *ᵥ x) =
      localUnitaryPhase E P K σ g
        (RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates E K σ hσ θ hθ (Intrinsic.Multiplicity.nativeMatrix E P) hH e x) := by
  obtain ⟨u, rfl⟩ := (RepresentationTheory.Hecke.RadialDilation.SplitScalarCoordinates.Realization.splitRationalCoordinates E K e).surjective x
  rw [← SplitUnitaryCoordinates.Intrinsic.rational_matrix_realizes_split_unitary]
  simp only [RepresentationTheory.Hecke.RadialDilation.SplitScalarSymplectic.Realization.rationalToSplitCoordinates, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  exact splitSymplecticCoordinates_unitary E P K σ hσ θ hθ hH g u

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalUnitaryPhase.Intrinsic
