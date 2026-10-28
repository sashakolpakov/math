import OAI.AlgebraicGeometry.ComplexPoints.IntegralTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffinePointSpectrum
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.QuasiFinite.Basic

/-! # Integral Characters -/

namespace OAI.AlgebraicGeometry.ComplexPoints.IntegralCharacters.ClosednessConstruction

/-! Closedness: lifting complex characters through integral algebra maps. -/

variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- A complex algebra character is determined by its kernel. -/
theorem character_eq_of_ker_eq (x y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    (h : RingHom.ker x.toRingHom = RingHom.ker y.toRingHom) : x = y := by
  ext a
  have ha : a - algebraMap ℂ A (x a) ∈ RingHom.ker x.toRingHom := by
    change x (a - algebraMap ℂ A (x a)) = 0
    simp
  rw [h] at ha
  change y (a - algebraMap ℂ A (x a)) = 0 at ha
  have he : y a - x a = 0 := by
    simpa using ha
  exact (sub_eq_zero.mp he).symm

/-- Every maximal ideal of a finite-type complex algebra is a character kernel. -/
theorem exists_character_of_maximal [Algebra.FiniteType ℂ B]
    (Q : Ideal B) [Q.IsMaximal] :
    ∃ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B, RingHom.ker x.toRingHom = Q := by
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let : Module.Finite ℂ (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ Q)
  let e : ℂ ≃ₐ[ℂ] (B ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ Q))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ Q), ?_⟩
  ext b
  change e.symm (Ideal.Quotient.mk Q b) = 0 ↔ b ∈ Q
  rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]

/-- An injective integral map into a finite-type complex algebra is surjective
on complex points. -/
theorem integral_comap_surjective [Algebra.FiniteType ℂ B]
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.IsIntegral)
    (hinj : Function.Injective f) : Function.Surjective (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f) := by
  intro y
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  let P := RingHom.ker y.toRingHom
  let : P.IsMaximal := Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_isMaximal y
  obtain ⟨Q, hQ, he⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := A) (S := B) P (by
      change RingHom.ker f.toRingHom ≤ P
      rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hinj]
      exact bot_le)
  let := hQ
  obtain ⟨x, hx⟩ := exists_character_of_maximal Q
  refine ⟨x, character_eq_of_ker_eq (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x) y ?_⟩
  change Ideal.comap f.toRingHom (RingHom.ker x.toRingHom) = P
  rw [hx]
  exact he

/-- Integral maps with finite-type source have finite fibers on complex points. -/
theorem integral_comap_finite_fiber [Algebra.FiniteType ℂ B]
    (f : A →ₐ[ℂ] B) (hf : f.toRingHom.IsIntegral) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) :
    (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f ⁻¹' {y}).Finite := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  have hft : f.toRingHom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f.comp_algebraMap.symm ▸ (RingHom.finiteType_algebraMap.mpr inferInstance))
  let : Algebra.FiniteType A B := hft
  let : Module.Finite A B := Algebra.IsIntegral.finite
  have hinj : Function.Injective (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum (A := B)) := fun x y h =>
    character_eq_of_ker_eq x y (congrArg PrimeSpectrum.asIdeal h)
  have hfin := (Algebra.QuasiFinite.finite_comap_preimage_singleton
    (S := B) (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y)).preimage hinj.injOn
  apply hfin.subset
  intro x hx
  change Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap f x = y at hx
  change PrimeSpectrum.comap f.toRingHom (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum x) = Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum y
  rw [← Foundations.Scheme.AffineComplexPoints.affineComplexPoints.toPrimeSpectrum_comap, hx]

/-- A regular function separates one character from a finite set of other characters. -/
theorem exists_separating_element
    (s : Set (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)) (hs : s.Finite) (p : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    ∃ b : B, ∀ q ∈ s, p b = q b → p = q := by
  classical
  let t := s \ {p}
  have ht : t.Finite := hs.subset Set.sdiff_subset
  let := ht.fintype
  have ha (q : t) : ∃ a : B, p a ≠ q.val a := by
    by_contra! h
    have he : p = q.val := AlgHom.ext h
    exact q.property.2 (Set.mem_singleton_iff.mpr he.symm)
  choose a ha using ha
  let b : B := ∏ q : t, (a q - algebraMap ℂ B (q.val (a q)))
  have hpb : p b ≠ 0 := by
    simp only [b, map_prod, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => sub_ne_zero.mpr (ha q))
  refine ⟨b, fun q hqs he => ?_⟩
  by_contra hpq
  let q' : t := ⟨q, hqs, fun h => hpq (Set.mem_singleton_iff.mp h).symm⟩
  have hqb : q b = 0 := by
    simp only [b, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ q')
    simp [q']
  exact hpb (he.trans hqb)

variable {R : Type*} [CommRing R] [Algebra ℂ R]
    [Algebra R B] [IsScalarTower ℂ R B]
    [IsDomain R] [IsIntegrallyClosed R] [IsDomain B] [Module.IsTorsionFree R B]
    [Algebra.IsIntegral R B] [Algebra.FiniteType ℂ B]

/-- Over a normal domain, every root of a specialized minimal polynomial
is realized by a complex point of the integral extension. -/
theorem minpoly_specialization_root_lifts (b : B) (y : Foundations.Scheme.AffineComplexPoints.affineComplexPoints R) (z : ℂ)
    (hz : ((minpoly R b).map y.toRingHom).IsRoot z) :
    ∃ x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B,
      Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap (IsScalarTower.toAlgHom ℂ R B) x = y ∧ x b = z := by
  let S := Algebra.adjoin R ({b} : Set B)
  have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
  let e : AdjoinRoot (minpoly R b) ≃ₐ[R] S := minpoly.equivAdjoin hb
  let χ : AdjoinRoot (minpoly R b) →ₐ[ℂ] ℂ :=
    AdjoinRoot.liftAlgHom (minpoly R b) y z (by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, AlgHom.toRingHom_eq_coe] using hz)
  let ψ : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S := χ.comp (e.symm.restrictScalars ℂ).toAlgHom
  let ι : S →ₐ[ℂ] B := S.val.restrictScalars ℂ
  have hι : ι.toRingHom.IsIntegral := fun a =>
    (Algebra.IsIntegral.isIntegral (R := R) a).tower_top (A := S)
  obtain ⟨x, hx⟩ := integral_comap_surjective ι hι Subtype.val_injective ψ
  refine ⟨x, ?_, ?_⟩
  · ext r
    have h := congrArg (fun q : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => q (algebraMap R S r)) hx
    change x (algebraMap R B r) = y r
    change x (algebraMap R B r) = χ (e.symm (algebraMap R S r)) at h
    simpa only [AlgEquiv.commutes, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of, χ]
      using h
  · let s : S := ⟨b, Algebra.subset_adjoin (Set.mem_singleton b)⟩
    have he : e (AdjoinRoot.root (minpoly R b)) = s := by
      apply Subtype.ext
      simp [e, minpoly.equivAdjoin, AdjoinRoot.Minpoly.toAdjoin, s]
    have h := congrArg (fun q : Foundations.Scheme.AffineComplexPoints.affineComplexPoints S => q s) hx
    change x b = χ (e.symm s) at h
    rw [← he, e.symm_apply_apply] at h
    simpa only [χ, AdjoinRoot.liftAlgHom_root] using h

end OAI.AlgebraicGeometry.ComplexPoints.IntegralCharacters.ClosednessConstruction
