import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.IntrinsicFamilyBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatModelPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalParameter

/-! # Arbitrary Local Parameter -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalParameter.GradedHilbert

noncomputable section

/-! Native Hilbert families over arbitrary local test rings have actual
bounded Hilbert parameters whenever their base map factors through a
Noetherian affine scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsNoetherianRing B]
variable [Algebra B A] {n N : ℕ} {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem exists_local_hilbert_parameter_of_base_factorization
    (c : Spec (.of B) ⟶ S) (a : Spec (.of A) ⟶ S)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap B A)) ≫ c = a)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a))
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    ∃ x : Over.mk a ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P),
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) = F := by
  let E := Intrinsic.AffineEquationModel.GradedHilbert.nativeAffineEquations a F
  let C := Intrinsic.AffineEquationModel.GradedHilbert.nativeEquationCoefficientRing E B
  let M := Intrinsic.FlatEquationModel.GradedHilbert.nativeLocalFlatEquationModel (B := B) E
  let R := M.R
  let I := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) (Intrinsic.AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)
  have : IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  have : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := M.flat
  let φ : R →+* A := algebraMap R A
  let ψ : B →+* R := (algebraMap C R).comp (algebraMap B C)
  have hψφ : φ.comp ψ = algebraMap B A := by
    apply RingHom.ext
    intro b
    change algebraMap R A (algebraMap C R (algebraMap B C b)) = algebraMap B A b
    rw [← IsScalarTower.algebraMap_apply C R A]
    rfl
  let aR : Spec (.of R) ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ c
  have hw : Spec.map (CommRingCat.ofHom φ) ≫ aR = a := by
    dsimp only [aR]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (φ.comp ψ)) ≫ c = a
    rw [hψφ]
    exact ha
  let b : Over.mk a ⟶ Over.mk aR := Over.homMk (Spec.map (CommRingCat.ofHom φ)) hw
  let G := Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n aR I
  have hPI : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := Intrinsic.FlatModelPolynomial.GradedHilbert.nativeLocalFlatEquationModel_hilbertPolynomial
    (B := B) E P hP
  obtain ⟨x, hx⟩ := Noetherian.LocalParameter.GradedHilbert.exists_noetherian_local_hilbert_parameter aR G P
    (Presentations.Flat.IntrinsicFamilyBaseChange.GradedHilbert.localFlat_nativeFamily_residue_polynomial I aR P hPI) N hN ι hr
  refine ⟨b ≫ x, ?_⟩
  rw [Hilbert.Functor.pullbackFamily_comp, hx]
  exact Presentations.Flat.IntrinsicFamilyBaseChange.GradedHilbert.nativeFamilyOfHomogeneousIdeal_pullback_eq I aR a b rfl F
    (Intrinsic.FlatEquationModel.GradedHilbert.nativeLocalFlatEquationModel_coordinates (B := B) E)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalParameter.GradedHilbert
