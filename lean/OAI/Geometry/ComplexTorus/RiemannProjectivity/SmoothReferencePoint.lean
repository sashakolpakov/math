import OAI.Geometry.ComplexTorus.RiemannProjectivity.QuotientLocalizationIs
import Mathlib.RingTheory.Smooth.Locus
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GraphRegular

/-! # Smooth Reference Point -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

/-! # RiemannProjectivity: smoothness at genuine algebraic points descends through localization -/

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

def pointPrime (q : A →ₐ[ℂ] ℂ) : PrimeSpectrum A :=
  ⟨RingHom.ker q.toRingHom, RingHom.ker_isPrime _⟩

theorem mem_smoothLocus_of_away [Algebra.FinitePresentation ℂ A]
    (q : A →ₐ[ℂ] ℂ) (s : A) (hs : q s ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away s)] :
    pointPrime q ∈ Algebra.smoothLocus ℂ A := by
  apply (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := ℂ) (A := A) (f := s)).mpr
    inferInstance
  exact hs

theorem mem_smoothLocus_of_localization [Algebra A B] [IsScalarTower ℂ A B]
    (r : A) [IsLocalization.Away r B] (q : B →ₐ[ℂ] ℂ)
    (hq : pointPrime q ∈ Algebra.smoothLocus ℂ B) :
    pointPrime (q.comp (Algebra.algHom ℂ A B)) ∈ Algebra.smoothLocus ℂ A := by
  rw [← Algebra.smoothLocus_comap_of_isLocalization (R := ℂ) (Af := B) r] at hq
  exact hq

theorem mem_smoothLocus_of_equiv (e : A ≃ₐ[ℂ] B) (q : B →ₐ[ℂ] ℂ)
    (hq : pointPrime (q.comp e.toAlgHom) ∈ Algebra.smoothLocus ℂ A) :
    pointPrime q ∈ Algebra.smoothLocus ℂ B := by
  let : Algebra B A := e.symm.toRingHom.toAlgebra
  let : IsScalarTower ℂ B A := IsScalarTower.of_algHom e.symm.toAlgHom
  let : IsLocalization.Away (1 : B) A := IsLocalization.of_le_isUnit_of_bijective
    (by simp [Algebra.algebraMapSubmonoid]) e.symm.bijective
  have h := mem_smoothLocus_of_localization (1 : B) (q.comp e.toAlgHom) hq
  have heq : (q.comp e.toAlgHom).comp (Algebra.algHom ℂ B A) = q := by
    ext b
    exact congrArg q (e.apply_symm_apply b)
  rwa [heq] at h

theorem quotient_mem_smoothLocus
    [Algebra A B] [IsScalarTower ℂ A B] [Algebra.FinitePresentation ℂ B] [IsNoetherianRing B]
    (r : A) [IsLocalization.Away r B] (I : Ideal A)
    (q : (B ⧸ I.map (algebraMap A B)) →ₐ[ℂ] ℂ)
    (s : B ⧸ I.map (algebraMap A B)) (hs : q s ≠ 0)
    [Algebra.Smooth ℂ (Localization.Away s)] :
    pointPrime (q.comp (Algebra.algHom ℂ (A ⧸ I) (B ⧸ I.map (algebraMap A B)))) ∈
      Algebra.smoothLocus ℂ (A ⧸ I) := by
  let : IsLocalization.Away (Ideal.Quotient.mk I r) (B ⧸ I.map (algebraMap A B)) :=
    QuotientLocalizationIs.Constructions.QuotientLocalization.isLocalization_away r I
  let : Algebra.FinitePresentation ℂ (B ⧸ I.map (algebraMap A B)) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian _)
  exact mem_smoothLocus_of_localization (Ideal.Quotient.mk I r) q
    (mem_smoothLocus_of_away q s hs)

end Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.ReferenceQuotientSmoothPoint

/-! # RiemannProjectivity: smoothness on an equation presentation descends to the original quotient -/

open OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {A : Type*} [CommRing A] [Algebra ℂ A]
  [Algebra.FinitePresentation ℂ A] [IsNoetherianRing A]

theorem exists_smooth_point (J I : Ideal A) (hJI : J ≤ I) (r : A ⧸ J)
    (q : Localization.Away r →ₐ[ℂ] ℂ)
    (hq : I.map ((algebraMap (A ⧸ J) (Localization.Away r)).comp (Ideal.Quotient.mk J)) ≤
      RingHom.ker q.toRingHom)
    (s : Localization.Away r) (hs : q s ≠ 0)
    (hsm : Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk
      (I.map ((algebraMap (A ⧸ J) (Localization.Away r)).comp (Ideal.Quotient.mk J))) s))) :
    ∃ qI : (A ⧸ I) →ₐ[ℂ] ℂ,
      (∀ a, qI (Ideal.Quotient.mk I a) = q (algebraMap (A ⧸ J) (Localization.Away r)
        (Ideal.Quotient.mk J a))) ∧ SmoothPointLocalization.pointPrime qI ∈ Algebra.smoothLocus ℂ (A ⧸ I) := by
  let K : Ideal (A ⧸ J) := I.map (Ideal.Quotient.mk J)
  let B := Localization.Away r
  have hmap : K.map (algebraMap (A ⧸ J) B) =
      I.map ((algebraMap (A ⧸ J) B).comp (Ideal.Quotient.mk J)) := by
    exact Ideal.map_map _ _
  have hk : K.map (algebraMap (A ⧸ J) B) ≤ RingHom.ker q.toRingHom := by
    rw [hmap]
    exact hq
  let qB : (B ⧸ K.map (algebraMap (A ⧸ J) B)) →ₐ[ℂ] ℂ :=
    Ideal.Quotient.liftₐ _ q hk
  let qK := qB.comp (Algebra.algHom ℂ ((A ⧸ J) ⧸ K) (B ⧸ K.map (algebraMap (A ⧸ J) B)))
  let : Algebra.FinitePresentation ℂ (A ⧸ J) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian _)
  let : Algebra.FinitePresentation ℂ B := Algebra.FinitePresentation.trans ℂ (A ⧸ J) B
  let : Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (K.map (algebraMap (A ⧸ J) B)) s)) := by
    rwa [hmap]
  have hqK : SmoothPointLocalization.pointPrime qK ∈ Algebra.smoothLocus ℂ ((A ⧸ J) ⧸ K) :=
    SmoothPointLocalization.quotient_mem_smoothLocus r K qB (Ideal.Quotient.mk _ s) hs
  let e : ((A ⧸ J) ⧸ K) ≃ₐ[ℂ] (A ⧸ I) := DoubleQuot.quotQuotEquivQuotOfLEₐ ℂ hJI
  let qI := qK.comp e.symm.toAlgHom
  refine ⟨qI, ?_, ?_⟩
  · intro a
    rfl
  · apply SmoothPointLocalization.mem_smoothLocus_of_equiv e qI
    have heq : qI.comp e.toAlgHom = qK := by
      ext a
      exact congrArg qK (e.symm_apply_apply a)
    rwa [heq]

end Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.ReferenceQuotientSmoothPoint

namespace Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.AffineGraphSmoothPoint

/-! # RiemannProjectivity: regular coordinate graphs give smooth points of the actual affine vanishing ideal -/

open Set _root_.Polynomial
open OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SmoothEquationPoint OAI.Geometry.ComplexTorus.RiemannProjectivity.JacobianLocalizationAt.Constructions.SplitPolynomialJacobian OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalizedGraph.Constructions.LocalizedGraphGerms OAI.Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.SmoothPointLocalization

variable {n m : ℕ}

theorem exists_smooth_point
    (F : Fin m → Polynomial (MvPolynomial (Fin n) ℂ)) (hF : ∀ j, F j ≠ 0)
    (x : Fin n → ℂ) (ψ : (Fin n → ℂ) → Fin m → ℂ)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hx : x ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hzero : ∀ y ∈ U, ∀ j, (F j).eval₂ (MvPolynomial.eval y) (ψ y j) = 0)
    (hderiv : ∀ j, ((F j).map (MvPolynomial.eval x)).derivative.eval (ψ x j) ≠ 0)
    (S : Set (Fin n ⊕ Fin m → ℂ)) (hS : ∀ y ∈ U, GraphGermsOn.Constructions.GraphGerms.graph ψ y ∈ S)
    (hrel : ∀ w ∈ S, ∀ j, MvPolynomial.eval w (JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)) = 0) :
    ∃ q : (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S) →ₐ[ℂ] ℂ,
      (∀ p, q (Ideal.Quotient.mk _ p) = MvPolynomial.eval (GraphGermsOn.Constructions.GraphGerms.graph ψ x) p) ∧
      SmoothPointLocalization.pointPrime q ∈ Algebra.smoothLocus ℂ
        (MvPolynomial (Fin n ⊕ Fin m) ℂ ⧸ MvPolynomial.vanishingIdeal ℂ S) := by
  obtain ⟨s, q, hq, hs, hsm⟩ := GraphRegular.Constructions.GraphVanishingIdeal.exists_smooth_point_neighborhood
    F hF x ψ hU hx hψ hzero hderiv S hS
  let J : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ) := Ideal.span (range (fun j => JacobianLocalizationAt.Constructions.SplitPolynomialJacobian.equation j (F j)))
  let I := MvPolynomial.vanishingIdeal ℂ S
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact fun w hw => hrel w hw j
  have hk : I.map (GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F) ≤ RingHom.ker q.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change q (GraphRegular.Constructions.GraphVanishingIdeal.polynomialMap F p) = 0
    rw [hq]
    exact hp (GraphGermsOn.Constructions.GraphGerms.graph ψ x) (hS x hx)
  obtain ⟨qI, hqI, hpoint⟩ := ReferenceQuotientSmoothPoint.exists_smooth_point
    J I hJI (JacobianLocalizationAt.Constructions.SmoothEquationPoint.presentation F).jacobian q hk s hs hsm
  refine ⟨qI, ?_, hpoint⟩
  intro p
  exact (hqI p).trans (hq p)

end Geometry.ComplexTorus.RiemannProjectivity.SmoothReferencePoint.Constructions.AffineGraphSmoothPoint

end

end OAI
