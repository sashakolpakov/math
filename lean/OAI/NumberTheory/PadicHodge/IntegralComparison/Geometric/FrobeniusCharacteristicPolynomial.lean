import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.FrobeniusEtale
import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateRank
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant
import OAI.NumberTheory.PadicHodge.IntegralComparison.TateDegreeResultantNorm
import OAI.NumberTheory.PadicHodge.IntegralComparison.NaturalResultantRigidity

/-! # Frobenius Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusCharacteristicPolynomial

noncomputable section

/-! The actual Tate Frobenius characteristic polynomial is the monic
integer geometric degree polynomial. Finite étale polynomial tests give
all resultant norms, which determine every root multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.TateModule OAI.NumberTheory.PadicHodge.IntegralComparison.AlgebraicTatePolynomialAction
open OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.DegreeResultant
open OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.TateNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TatePolynomialDeterminant

variable (p : ℕ) [Fact p.Prime]
  (A : Over (Spec (.of (ZMod p)))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

abbrev geometricScheme := AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod p) A

local instance geometricGroup : GrpObj (geometricScheme p A) :=
  inferInstanceAs (GrpObj (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod p) A))

local instance geometricCommutative : IsCommMonObj (geometricScheme p A) :=
  inferInstanceAs (IsCommMonObj (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.geometricFiberOver (ZMod p) A))

local instance : IsProper (geometricScheme p A).hom :=
  inferInstanceAs (IsProper (Limits.pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod p))))

local instance : Smooth (geometricScheme p A).hom :=
  inferInstanceAs (Smooth (Limits.pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod p))))

local instance : GeometricallyIntegral (geometricScheme p A).hom :=
  inferInstanceAs (GeometricallyIntegral
    (Limits.pullback.snd A.hom (AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod p))))

local instance : IsIntegral (geometricScheme p A).left :=
  GeometricallyIntegral.isIntegral_of_subsingleton (geometricScheme p A).hom

abbrev geometricFrobenius : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd (geometricScheme p A) :=
  AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod p) A (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod p) A)

def integerFrobeniusPolynomial : Polynomial ℤ :=
  DegreeResultant.integerPolynomial (geometricScheme p A) (geometricFrobenius p A)

theorem integerFrobeniusPolynomial_monic : (integerFrobeniusPolynomial p A).Monic :=
  DegreeResultant.integerPolynomial_monic _ _

theorem integerFrobeniusPolynomial_natDegree :
    (integerFrobeniusPolynomial p A).natDegree =
      2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (geometricScheme p A).hom :=
  DegreeResultant.integerPolynomial_natDegree _ _

theorem ell_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (ℓ : AlgebraicClosure (ZMod p)) ≠ 0 := by
  have hℓ : (ℓ : ZMod p) ≠ 0 := by
    intro hz
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp
      ((ZMod.natCast_eq_zero_iff ℓ p).mp hz)).symm
  intro hz
  apply hℓ
  apply (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
  simpa only [map_natCast, map_zero] using hz

variable (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

def tateFrobenius : Module.End ℤ_[ℓ] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points (geometricScheme p A)) ℓ) :=
  Integral.TateNaturality.tateAction ℓ (geometricScheme p A) (geometricFrobenius p A)

include hℓp

theorem native_finite : Module.Finite ℤ_[ℓ]
    (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points (geometricScheme p A)) ℓ) :=
  TateModule.finite (geometricScheme p A) ℓ (ell_ne_zero p ℓ hℓp)

theorem native_free : Module.Free ℤ_[ℓ]
    (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := TateModule.Points (geometricScheme p A)) ℓ) :=
  TateModule.free (geometricScheme p A) ℓ (ell_ne_zero p ℓ hℓp)

theorem rational_charpoly_natDegree :
    letI := native_finite p A ℓ hℓp
    letI := native_free p A ℓ hℓp
    ((Integral.TateNaturality.tateAction ℓ (geometricScheme p A) (geometricFrobenius p A)).baseChange ℚ_[ℓ]).charpoly.natDegree =
      2 * AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (geometricScheme p A).hom := by
  let := native_finite p A ℓ hℓp
  let := native_free p A ℓ hℓp
  rw [LinearMap.charpoly_baseChange, (LinearMap.charpoly_monic _).natDegree_map,
    LinearMap.charpoly_natDegree]
  exact TateRank.finrank (geometricScheme p A) ℓ (ell_ne_zero p ℓ hℓp)

theorem resultant_norm (R : Polynomial ℕ) (hR : ¬ p ∣ R.coeff 0) :
    letI := native_finite p A ℓ hℓp
    letI := native_free p A ℓ hℓp
    ‖((Integral.TateNaturality.tateAction ℓ (geometricScheme p A) (geometricFrobenius p A)).baseChange ℚ_[ℓ]).charpoly.resultant
      (R.map (Nat.castRingHom ℚ_[ℓ]))‖ =
    ‖((integerFrobeniusPolynomial p A).map (Int.castRingHom ℚ_[ℓ])).resultant
      (R.map (Nat.castRingHom ℚ_[ℓ]))‖ := by
  let := native_finite p A ℓ hℓp
  let := native_free p A ℓ hℓp
  have hRk : (R.coeff 0 : ZMod p) ≠ 0 := by
    intro hz
    exact hR ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  obtain ⟨hfin, hsurj, het⟩ := IntegralComparison.Polynomial.FrobeniusEtale.finite_etale (ZMod p) A R hRk
  let : IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd (geometricScheme p A) (geometricFrobenius p A) R).toMul.hom.hom.left := hfin
  let : Surjective (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd (geometricScheme p A) (geometricFrobenius p A) R).toMul.hom.hom.left := hsurj
  let : Etale (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd (geometricScheme p A) (geometricFrobenius p A) R).toMul.hom.hom.left := het
  exact TateDegreeResultantNorm.resultant_norm (geometricScheme p A) ℓ (ell_ne_zero p ℓ hℓp)
    (geometricFrobenius p A) R

theorem rational_charpoly :
    letI := native_finite p A ℓ hℓp
    letI := native_free p A ℓ hℓp
    ((Integral.TateNaturality.tateAction ℓ (geometricScheme p A) (geometricFrobenius p A)).baseChange ℚ_[ℓ]).charpoly =
      (integerFrobeniusPolynomial p A).map (Int.castRingHom ℚ_[ℓ]) := by
  let := native_finite p A ℓ hℓp
  let := native_free p A ℓ hℓp
  apply NaturalResultantRigidity.monic_eq_of_natural_resultant_norm ℓ p hℓp
    _ _ (LinearMap.charpoly_monic _) ((integerFrobeniusPolynomial_monic p A).map _)
  · rw [(integerFrobeniusPolynomial_monic p A).natDegree_map,
      integerFrobeniusPolynomial_natDegree]
    exact rational_charpoly_natDegree p A ℓ hℓp
  · exact resultant_norm p A ℓ hℓp

theorem integral_charpoly_map :
    letI := native_finite p A ℓ hℓp
    letI := native_free p A ℓ hℓp
    (Integral.TateNaturality.tateAction ℓ (geometricScheme p A)
      (geometricFrobenius p A)).charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      (integerFrobeniusPolynomial p A).map (Int.castRingHom ℚ_[ℓ]) := by
  let := native_finite p A ℓ hℓp
  let := native_free p A ℓ hℓp
  rw [← LinearMap.charpoly_baseChange]
  exact rational_charpoly p A ℓ hℓp

theorem tateFrobenius_charpoly_map :
    letI := native_finite p A ℓ hℓp
    letI := native_free p A ℓ hℓp
    (tateFrobenius p A ℓ).charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      (integerFrobeniusPolynomial p A).map (Int.castRingHom ℚ_[ℓ]) :=
  integral_charpoly_map p A ℓ hℓp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusCharacteristicPolynomial
