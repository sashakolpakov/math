import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalPresentationTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalMap

/-! # Principal Coefficient Presentation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalCoefficientPresentation

noncomputable section

/-! Denominators of an arbitrary affine open immersion lift to finite coefficients. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem coefficient_principalMap_bijective
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B] (D : Subalgebra C R) (φ : A →ₐ[C] B)
    (a : D ⊗[C] A)
    (h : PrincipalMap.PrincipalMapCriterion (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom
      (Coefficient.TensorMaps.coefficientTensorMap D a)) :
    Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R)
      (Algebra.TensorProduct.map (AlgHom.id D D) φ) a) := by
  let φR := Algebra.TensorProduct.map (AlgHom.id R R) φ
  let φD := Algebra.TensorProduct.map (AlgHom.id D D) φ
  let φDR := Algebra.TensorProduct.map (AlgHom.id R R) φD
  let eA := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := A) D
  let eB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D
  have hw (x : R ⊗[D] (D ⊗[C] A)) : eB (φDR x) = φR (eA x) :=
    DFunLike.congr_fun (Coefficient.BaseChangeComparison.coefficientBaseChangeIso_natural D φ) x
  have hh : PrincipalMap.PrincipalMapCriterion φR.toRingHom (eA ((1 : R) ⊗ₜ[D] a)) := by
    rw [show eA ((1 : R) ⊗ₜ[D] a) = Coefficient.TensorMaps.coefficientTensorMap D a from
      Coefficient.BaseChangeComparison.coefficientBaseChangeIso_one_tmul D a]
    exact h
  have hb := PrincipalMap.principalMapCriterion_of_conjugate
    (A := R ⊗[D] (D ⊗[C] A)) (B := R ⊗[D] (D ⊗[C] B))
    (A' := R ⊗[C] A) (B' := R ⊗[C] B) φDR.toRingHom φR.toRingHom
    eA.toRingEquiv eB.toRingEquiv hw ((1 : R) ⊗ₜ[D] a) hh
  exact (PrincipalMap.principalBaseChangeMap_bijective_iff_criterion φD a).mpr hb

theorem exists_affine_principal_coefficient_presentation
    {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
    [Algebra C R] [Algebra C A] [Algebra C B] (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      ∃ (k : ℕ) (f : Fin k → D ⊗[C] A),
        Ideal.span (Set.range (fun i => (1 : R) ⊗ₜ[D]
          Algebra.TensorProduct.map (AlgHom.id D D) φ (f i))) = ⊤ ∧
        ∀ i, Function.Bijective (PrincipalLocalizationNaturality.principalBaseChangeMap (R := R)
          (Algebra.TensorProduct.map (AlgHom.id D D) φ) (f i)) := by
  let φR := Algebra.TensorProduct.map (AlgHom.id R R) φ
  obtain ⟨k, fR, hcover, hiso⟩ := AffineOpen.ImmersionPresentation.exists_finite_principal_openImmersion_presentation φR.toRingHom
  obtain ⟨D, hED, hD, hd⟩ := Finite.TensorCoefficients.exists_finite_tensor_coefficients fR E hE
  choose f hf using hd
  let φD := Algebra.TensorProduct.map (AlgHom.id D D) φ
  let eB := Coefficient.BaseChangeComparison.coefficientBaseChangeIso (A := B) D
  refine ⟨D, hED, hD, k, f, ?_, ?_⟩
  · apply PrincipalPresentationTransport.principal_cover_of_ringEquiv (A := R ⊗[D] (D ⊗[C] B)) (B := R ⊗[C] B)
      eB.toRingEquiv (fun i => (1 : R) ⊗ₜ[D] φD (f i))
    have heq : (fun i => eB ((1 : R) ⊗ₜ[D] φD (f i))) = fun i => φR (fR i) := by
      funext i
      exact (Coefficient.BaseChangeComparison.coefficientBaseChangeIso_one_tmul D (φD (f i))).trans
        ((NaturalTensorMapDescent.coefficientTensorMap_natural D φ (f i)).trans (congrArg φR (hf i)))
    change Ideal.span (Set.range (fun i => eB ((1 : R) ⊗ₜ[D] φD (f i)))) = ⊤
    rw [heq]
    exact hcover
  · intro i
    apply coefficient_principalMap_bijective D φ (f i)
    rw [show Coefficient.TensorMaps.coefficientTensorMap D (f i) = fR i from hf i]
    exact (PrincipalMap.localizationMap_bijective_iff_criterion
      (P := Localization.Away (fR i)) (Q := Localization.Away (φR (fR i)))
      φR.toRingHom (fR i)).mp (hiso i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PrincipalCoefficientPresentation
