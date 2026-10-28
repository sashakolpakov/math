import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData
import OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport

/-! # Rational Phase Column -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn.Intrinsic

noncomputable section

section

/-! The actual rational special-unitary action on the signed multiplicity
space preserves its trace pairing. Express it in the same symplectic
coordinates used by the native period and finite dilation construction. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity
open scoped Classical _root_.Matrix

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))

def rationalUnitaryEnd (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) : Module.End ℚ (Fin 3 → E) :=
  (Matrix.SpecialLinearGroup.toLin' g.val).toLinearMap.restrictScalars ℚ

omit [IsGalois ℚ E] in
theorem rationalUnitaryEnd_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) :
    rationalUnitaryEnd E P g x = g.val.val.mulVec x := rfl

theorem nativeTensorPairing_unitary (v : Multiplicity.Odd.Sign E) (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (x y : Fin 3 → E) :
    Intrinsic.Multiplicity.nativeTensorPairing E P v (rationalUnitaryEnd E P g x) (rationalUnitaryEnd E P g y) =
      Intrinsic.Multiplicity.nativeTensorPairing E P v x y :=
  congrArg (fun z : E => Intrinsic.Multiplicity.nativeCoefficient E P v * z) (g.property x y)

def rationalUnitaryMatrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    Matrix (Sum (Fin s × Fin 3) (Fin s × Fin 3)) (Sum (Fin s × Fin 3) (Fin s × Fin 3)) ℚ :=
  LinearMap.toMatrix' ((e.toLinearMap.comp (rationalUnitaryEnd E P g)).comp e.symm.toLinearMap)

omit [IsGalois ℚ E] in
theorem rationalUnitaryMatrix_apply (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) :
    rationalUnitaryMatrix E P e g *ᵥ e x = e (rationalUnitaryEnd E P g x) := by
  rw [rationalUnitaryMatrix, LinearMap.toMatrix'_mulVec]
  simp

omit [IsGalois ℚ E] in
theorem rationalUnitaryMatrix_one : rationalUnitaryMatrix E P e 1 = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  simp only [Matrix.toLin'_apply, rationalUnitaryMatrix_apply, rationalUnitaryEnd_apply,
    OneMemClass.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

omit [IsGalois ℚ E] in
theorem rationalUnitaryMatrix_mul (g h : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    rationalUnitaryMatrix E P e (g * h) = rationalUnitaryMatrix E P e g * rationalUnitaryMatrix E P e h := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, rationalUnitaryMatrix_apply,
    rationalUnitaryEnd_apply, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]

def nativeRationalSymplectic (v : Multiplicity.Odd.Sign E)
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y)) :
    Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin s × Fin 3) ℚ where
  toFun g := ⟨rationalUnitaryMatrix E P e g, by
    apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
    intro z w
    obtain ⟨x, rfl⟩ := e.surjective z
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [rationalUnitaryMatrix_apply, rationalUnitaryMatrix_apply, he, he,
      nativeTensorPairing_unitary]⟩
  map_one' := Subtype.ext (rationalUnitaryMatrix_one E P e)
  map_mul' g h := Subtype.ext (rationalUnitaryMatrix_mul E P e g h)

theorem nativeRationalSymplectic_apply (v : Multiplicity.Odd.Sign E)
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (x : Fin 3 → E) :
    (nativeRationalSymplectic E P e v he g).val *ᵥ e x = e (g.val.val *ᵥ x) :=
  rationalUnitaryMatrix_apply E P e g x

end

/-! Columns of the rational phase matrix in the retained original basis. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

open OAI.RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Multiplicity

attribute [local instance] Intrinsic.Multiplicity.nativePlaceDecidableEq Intrinsic.Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
  (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (Fin s × Fin 3) (Fin s × Fin 3) → ℚ))

omit [IsGalois ℚ E] in
theorem rationalUnitaryMatrix_column (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (i j : (Fin s × Fin 3) ⊕ (Fin s × Fin 3)) :
    rationalUnitaryMatrix E P e γ i j = e (γ.val.val *ᵥ e.symm (Pi.single j 1)) i := by
  have h := rationalUnitaryMatrix_apply E P e γ (e.symm (Pi.single j 1))
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h
  exact congr_fun h i

theorem nativeRationalSymplectic_val (v : Multiplicity.Odd.Sign E)
    (he : ∀ x y, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (e x) (e y) =
      Algebra.trace ℚ E (P.imaginaryScalar * Intrinsic.Multiplicity.nativeTensorPairing E P v x y))
    (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (nativeRationalSymplectic E P e v he γ).val = rationalUnitaryMatrix E P e γ := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPhaseColumn.Intrinsic
