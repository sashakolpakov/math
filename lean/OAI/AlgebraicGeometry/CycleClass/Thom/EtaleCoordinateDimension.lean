import OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.FiniteTypeSchemeTopology
import OAI.AlgebraicGeometry.Foundations.Scheme.OpenFunctionField
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Etale Coordinate Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension.Constructions

noncomputable section

/-! The number of etale polynomial coordinates is the actual smooth
dimension. The equality follows from the base-change theorem for
Kahler differentials and the native affine dimension comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.SmoothAffineGlobalCoordinates.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem etale_generic_rank (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) A]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) A] : Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A = n := by
  let P := MvPolynomial (Fin n) ℂ
  let q : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  have hfin : Module.finrank P Ω[P⁄ℂ] = n := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis ℂ (Fin n))
  calc
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A = Module.rankAtStalk Ω[A⁄ℂ] q := rfl
    _ = Module.rankAtStalk Ω[P⁄ℂ] (q.comap (algebraMap P A)) :=
      Module.rankAtStalk_isBaseChange (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ P A) q
    _ = Module.finrank P Ω[P⁄ℂ] := by simp
    _ = n := hfin

theorem affine_coordinate_dimension (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = n := by
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  obtain ⟨χ, _⟩ := Finite.TypeCharacters.Constructions.exists_character_ne_zero ℂ Γ(X.left, ⊤) 1 one_ne_zero
  have h := SmoothAffineGlobalCoordinates.Constructions.affineNative_modelDimension X ((ComplexPoints.Analytic.AffineSchemePointTopology.affineNativePointHomeomorph X).symm χ)
  exact h.trans (etale_generic_rank Γ(X.left, ⊤) n)

theorem open_coordinate_dimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (j : X ⟶ V.toOver) [IsOpenImmersion j.left]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [IsScalarTower ℂ (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)]
    [Algebra.FormallyEtale (MvPolynomial (Fin n) ℂ) Γ(X.left, ⊤)] : n = V.complexDimension := by
  let : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
  have hx := affine_coordinate_dimension X n
  have hd := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion j.left V.structureMap
  have hj : j.left ≫ V.structureMap = X.hom := j.w
  rw [hj, Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension] at hd
  rw [← Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension V] at hd
  exact hx.symm.trans hd

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EtaleCoordinateDimension.Constructions
