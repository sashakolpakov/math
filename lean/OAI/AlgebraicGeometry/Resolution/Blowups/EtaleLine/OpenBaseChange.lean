import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RefinementPullback

/-! # Open Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.OpenBaseChange.Construction

noncomputable section

/-! Actual pointed open base changes of relative étale lines over the original field. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

attribute [local instance] Polynomial.algebra

theorem exists_etale_line_open_base_change
    {k H A R : Type u} [CommRing k] [CommRing H] [CommRing A] [CommRing R]
    [Algebra k H] [Algebra k A] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    (φ : H →ₐ[k] A) [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))]
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap φ.toRingHom q = PrimeSpectrum.comap (algebraMap H R) p) :
    ∃ (U : CommRingCat.{u}) (_ : Algebra k U) (_ : Algebra A U) (_ : Algebra A[X] U),
      IsScalarTower k A U ∧ IsScalarTower A A[X] U ∧ Algebra.Etale A[X] U ∧
      ∃ f : R →ₐ[k] U, IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) ∧
        f (algebraMap H[X] R X) = algebraMap A[X] U X ∧
        (∀ h : H, f (algebraMap H R h) = algebraMap A U (φ h)) ∧
        ∃ Q : PrimeSpectrum U, PrimeSpectrum.comap f.toRingHom Q = p ∧
          PrimeSpectrum.comap (algebraMap A U) Q = q := by
  let : Algebra H A := φ.toRingHom.toAlgebra
  let U := CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing (H := H) (B := A) (R := R)
  let : Algebra k U := ((algebraMap A U).comp (algebraMap k A)).toAlgebra
  let : SMul k U := (inferInstance : Algebra k U).toSMul
  let : Module k U := Algebra.toModule
  let : IsScalarTower k A U := IsScalarTower.of_algebraMap_eq' (R := k) (S := A) (A := U) rfl
  let : Algebra.Etale A[X] U := inferInstanceAs (Algebra.Etale A[X] (A[X] ⊗[H[X]] R))
  let r : R →+* U := (Algebra.TensorProduct.includeRight : R →ₐ[H[X]] U).toRingHom
  have hcoeff (h : H) : r (algebraMap H R h) = algebraMap A U (φ h) :=
    CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing_constants (H := H) (B := A) (R := R) h
  let f : R →ₐ[k] U :=
    { toRingHom := r
      commutes' := fun c => by
        change r (algebraMap k R c) = algebraMap A U (algebraMap k A c)
        rw [IsScalarTower.algebraMap_apply k H R, hcoeff, φ.commutes] }
  have hpb := RefinementPullback.Construction.etaleLineCoefficientRefinementRing_isPullback (H := H) (B := A) (R := R)
  have ho : IsOpenImmersion (Spec.map (CommRingCat.ofHom r)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb inferInstance
  obtain ⟨Q, hQA, hQR⟩ := Scheme.exists_preimage_of_isPullback hpb q p hq
  exact ⟨.of U, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    f, ho, CoefficientRefinement.Construction.etaleLineCoefficientRefinementRing_coordinate (H := H) (B := A) (R := R), hcoeff, Q, hQR, hQA⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.OpenBaseChange.Construction
