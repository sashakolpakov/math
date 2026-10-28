import OAI.NumberTheory.PadicHodge.IntegralComparison.Geometric.FrobeniusCharacteristicPolynomial
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleTateCharacteristicPolynomial

/-! # Etale Integer Characteristic Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleIntegerCharacteristicPolynomial.Geometric.AbelianModel

noncomputable section

/-! The original rational étale Frobenius of a GeometricComparison abelian model has
a single monic integer characteristic polynomial, independent of ℓ.
The polynomial is constructed from the actual geometric degree law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)

attribute [local instance] GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_group GeometricComparison.Geometry.AbelianH1Model.geometricSpecialFiber_commutative

local instance : IsProper A.geometricSpecialFiber.hom :=
  inferInstanceAs (IsProper
    (Limits.pullback.snd A.specialFiber.scheme.hom (OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

local instance : Smooth A.geometricSpecialFiber.hom :=
  inferInstanceAs (Smooth
    (Limits.pullback.snd A.specialFiber.scheme.hom (OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

local instance : GeometricallyIntegral A.geometricSpecialFiber.hom := by
  let : GeometricallyIntegral A.specialFiber.scheme.hom := A.specialFiber_geometricallyIntegral
  exact inferInstanceAs (GeometricallyIntegral
    (Limits.pullback.snd A.specialFiber.scheme.hom (OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Frobenius.Construction.algebraicClosureBase (ZMod q))))

local instance : IsIntegral A.geometricSpecialFiber.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.geometricSpecialFiber.hom

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeGeometricFrobenius : OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.geometricSpecialFiber :=
  OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphism.GeometricEmbedding.Construction.algebraicEndGeometricBaseChange (ZMod q) A.specialFiber.scheme
    (OAI.AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial : Polynomial ℤ :=
  Geometric.DegreeResultant.integerPolynomial A.geometricSpecialFiber A.nativeGeometricFrobenius

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_monic : A.nativeIntegerFrobeniusPolynomial.Monic := by
  exact Geometric.DegreeResultant.integerPolynomial_monic _ _

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_tate_charpoly_degree (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_tate_finite ℓ hℓq
    letI := A.native_tate_free ℓ hℓq
    (A.nativeTateFrobenius ℓ).charpoly.natDegree = A.nativeIntegerFrobeniusPolynomial.natDegree := by
  let := A.native_tate_finite ℓ hℓq
  let := A.native_tate_free ℓ hℓq
  rw [LinearMap.charpoly_natDegree, GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial, Geometric.DegreeResultant.integerPolynomial_natDegree]
  exact Geometric.TateRank.finrank A.geometricSpecialFiber ℓ
    (GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_polynomial_finite_etale (R : Polynomial ℕ) (hR : ¬ q ∣ R.coeff 0) :
    IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left ∧
    Surjective (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left ∧
    AlgebraicGeometry.Etale (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left := by
  let := A.specialFiber_geometricallyIntegral
  have hRk : (R.coeff 0 : ZMod q) ≠ 0 := fun hz => hR ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  exact IntegralComparison.Polynomial.FrobeniusEtale.finite_etale (ZMod q) A.specialFiber.scheme R hRk

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_points_tate_finite (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    Module.Finite ℤ_[ℓ]
      (OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A.geometricSpecialFiber) ℓ) := by
  have h := A.native_tate_finite ℓ hℓq
  dsimp only [GeometricComparison.Geometry.AbelianH1Model.NativeTate] at h
  exact h

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_points_tate_free (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    Module.Free ℤ_[ℓ]
      (OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := Geometric.TateModule.Points A.geometricSpecialFiber) ℓ) := by
  have h := A.native_tate_free ℓ hℓq
  dsimp only [GeometricComparison.Geometry.AbelianH1Model.NativeTate] at h
  exact h

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_tate_resultant_norm (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (R : Polynomial ℕ) (hR : ¬ q ∣ R.coeff 0) :
    letI := A.native_tate_finite ℓ hℓq
    letI := A.native_tate_free ℓ hℓq
    ‖((A.nativeTateFrobenius ℓ).charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ])).resultant
      (R.map (Nat.castRingHom ℚ_[ℓ]))‖ =
      ‖(A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[ℓ])).resultant
        (R.map (Nat.castRingHom ℚ_[ℓ]))‖ := by
  let := A.native_tate_finite ℓ hℓq
  let := A.native_tate_free ℓ hℓq
  let := A.native_points_tate_finite ℓ hℓq
  let := A.native_points_tate_free ℓ hℓq
  obtain ⟨hfin, hsurj, het⟩ := A.native_polynomial_finite_etale R hR
  let : IsFinite (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left := hfin
  let : Surjective (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left := hsurj
  let : AlgebraicGeometry.Etale (IntegralComparison.Polynomial.DegreeGeometry.Law.naturalEnd A.geometricSpecialFiber A.nativeGeometricFrobenius R).toMul.hom.hom.left := het
  have h := TateDegreeResultantNorm.resultant_norm A.geometricSpecialFiber ℓ
    (GeometricComparison.Geometry.AbelianH1Model.ell_ne_zero_in_geometricField ℓ hℓq) A.nativeGeometricFrobenius R
  rw [LinearMap.charpoly_baseChange] at h
  dsimp only [GeometricComparison.Geometry.AbelianH1Model.nativeTateFrobenius, GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial, GeometricComparison.Geometry.AbelianH1Model.nativeGeometricFrobenius] at h ⊢
  exact h

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_tate_charpoly_eq_integer (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_tate_finite ℓ hℓq
    letI := A.native_tate_free ℓ hℓq
    (A.nativeTateFrobenius ℓ).charpoly.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) =
      A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[ℓ]) := by
  let := A.native_tate_finite ℓ hℓq
  let := A.native_tate_free ℓ hℓq
  apply NaturalResultantRigidity.monic_eq_of_natural_resultant_norm ℓ q hℓq
    _ _ ((LinearMap.charpoly_monic _).map _) (A.nativeIntegerFrobeniusPolynomial_monic.map _)
  · rw [(LinearMap.charpoly_monic _).natDegree_map,
      A.nativeIntegerFrobeniusPolynomial_monic.natDegree_map]
    exact A.native_tate_charpoly_degree ℓ hℓq
  · exact A.native_tate_resultant_norm ℓ hℓq

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.native_etale_charpoly_eq_integer (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_etale_finite ℓ hℓq
    (A.etaleFrobenius ℓ).toLinearMap.charpoly =
      A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[ℓ]) := by
  let := A.native_etale_finite ℓ hℓq
  let := A.native_tate_finite ℓ hℓq
  let := A.native_tate_free ℓ hℓq
  exact (A.native_etale_charpoly_eq_tate ℓ hℓq).trans
    (A.native_tate_charpoly_eq_integer ℓ hℓq)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_natDegree (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    letI := A.native_etale_finite ℓ hℓq
    A.nativeIntegerFrobeniusPolynomial.natDegree = Module.finrank ℚ_[ℓ] (A.Etale ℓ) := by
  let := A.native_etale_finite ℓ hℓq
  rw [← A.nativeIntegerFrobeniusPolynomial_monic.natDegree_map (Int.castRingHom ℚ_[ℓ]),
    ← A.native_etale_charpoly_eq_integer ℓ hℓq, LinearMap.charpoly_natDegree]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.EtaleIntegerCharacteristicPolynomial.Geometric.AbelianModel
