import OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil
import Mathlib.RingTheory.Etale.Basic

/-! # Nil Lifting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.NilLifting

noncomputable section

/-!
# IntegralComparison: unique lifts of étale charts through nil ideals

The kernel need only consist of nilpotent elements. Finite presentation
reduces uniqueness to a finitely generated nilpotent subideal.
-/

universe u v w z

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B] {C : Type z} [CommRing C] [Algebra R C]

theorem lift_unique [Algebra.FinitePresentation R A] [Algebra.FormallyUnramified R A]
    (f : B →ₐ[R] C) (hnil : ∀ b ∈ RingHom.ker f.toRingHom, IsNilpotent b)
    (g₁ g₂ : A →ₐ[R] B) (h : f.comp g₁ = f.comp g₂) : g₁ = g₂ := by
  classical
  obtain ⟨n, q, hq, _⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let d : Fin n → B := fun i => g₁ (q (MvPolynomial.X i)) - g₂ (q (MvPolynomial.X i))
  let I : Ideal B := Ideal.span (Set.range d)
  have hI : I ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro b ⟨i, rfl⟩
    change f (g₁ (q (MvPolynomial.X i)) - g₂ (q (MvPolynomial.X i))) = 0
    have hi : f (g₁ (q (MvPolynomial.X i))) = f (g₂ (q (MvPolynomial.X i))) :=
      AlgHom.congr_fun h (q (MvPolynomial.X i))
    rw [map_sub, hi, sub_self]
  have hfg : I.FG := Submodule.fg_span (Set.finite_range d)
  have hnilI : IsNilpotent I := hfg.isNilpotent_iff_le_nilradical.mpr (fun b hb => hnil b (hI hb))
  apply Algebra.FormallyUnramified.lift_unique I hnilI g₁ g₂
  have hq' : ((Ideal.Quotient.mkₐ R I).comp g₁).comp q =
      ((Ideal.Quotient.mkₐ R I).comp g₂).comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span (Set.mem_range_self i)
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := hq a
  exact AlgHom.congr_fun hq' b

theorem existsUnique_lift [Algebra.FinitePresentation R A] [Algebra.FormallyEtale R A]
    (a : A →ₐ[R] C) (f : B →ₐ[R] C) (hf : Function.Surjective f)
    (hnil : ∀ b ∈ RingHom.ker f.toRingHom, IsNilpotent b) :
    ∃! g : A →ₐ[R] B, f.comp g = a := by
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting.exists_lift a f hf hnil
  exact ⟨g, hg, fun g' hg' => NilLifting.lift_unique f hnil g' g (hg'.trans hg.symm)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.NilLifting
