import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPolynomialExtension
import Mathlib.RingTheory.Polynomial.Quotient

/-! # Linear Prime Ideal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPrimeIdeal

noncomputable section

/-! The inverse cone of an integral projective support has a prime
homogeneous ideal under any independent linear projection coordinate map. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Projection

theorem polynomial_extension {R ι : Type} [CommRing R] (P : Ideal R) [P.IsPrime] :
    (P.map (MvPolynomial.C : R →+* MvPolynomial ι R)).IsPrime := by
  apply (Ideal.Quotient.isDomain_iff_prime _).mp
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) P
  exact Function.Injective.isDomain e.symm e.symm.injective

theorem of_equivalence {R S ι : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (e : S ≃+* MvPolynomial ι R)
    (he : ∀ r, e (f r) = MvPolynomial.C r) (P : Ideal R) [P.IsPrime] : (P.map f).IsPrime := by
  let Q := P.map (MvPolynomial.C : R →+* MvPolynomial ι R)
  let : Q.IsPrime := polynomial_extension P
  have hcomp : e.toRingHom.comp f = MvPolynomial.C := RingHom.ext he
  have hmap : (P.map f).map e.toRingHom = Q := by rw [Ideal.map_map, hcomp]
  have hpre : Q.comap e.toRingHom = P.map f := by
    rw [← hmap]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  rw [← hpre]
  infer_instance

theorem comap_of_equivalence {R S ι : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (e : S ≃+* MvPolynomial ι R)
    (he : ∀ r, e (f r) = MvPolynomial.C r) (P : Ideal R) : (P.map f).comap f = P := by
  apply le_antisymm _ Ideal.le_comap_map
  intro r hr
  have hcomp : e.toRingHom.comp f = MvPolynomial.C := RingHom.ext he
  have hmap : (P.map f).map e.toRingHom = P.map MvPolynomial.C := by rw [Ideal.map_map, hcomp]
  have hm : e (f r) ∈ (P.map f).map e.toRingHom := Ideal.mem_map_of_mem e.toRingHom hr
  rw [hmap, he] at hm
  have hc := (MvPolynomial.mem_map_C_iff.mp hm) 0
  simpa only [MvPolynomial.coeff_zero_C] using hc

theorem map_isPrime {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (P : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m)) [P.IsPrime] :
    (P.map (HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property)).toRingHom).IsPrime := by
  obtain ⟨ι, _, e, he⟩ := LinearPolynomialExtension.exists_equivalence L hL
  exact of_equivalence _ e.toRingEquiv he P

theorem comap_map {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)
    (hL : LinearIndependent ℂ L) (P : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m)) :
    (P.map (HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property)).toRingHom).comap
      (HomogeneousCoordinateMap.ofForms (fun i => (L i).val) (fun i => (L i).property)).toRingHom = P := by
  obtain ⟨ι, _, e, he⟩ := LinearPolynomialExtension.exists_equivalence L hL
  exact comap_of_equivalence _ e.toRingEquiv he P

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearPrimeIdeal
