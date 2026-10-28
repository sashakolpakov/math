import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Noetherian.Nilpotent

/-! # Smooth Nil -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting

noncomputable section

/-!
# Lifting smooth affine charts across nil ideals

A map from a finitely presented algebra into a quotient already factors
through a quotient by a finitely generated subideal of the kernel.
If the kernel consists of nilpotent elements, this smaller ideal is
nilpotent, so formal smoothness supplies a lift. No uniform nilpotence
bound on the original kernel is required.
-/

universe u v w z

variable {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {C : Type z} [CommRing C] [Algebra R C]

/-- Only finitely many relations obstruct a lift from a finitely presented algebra. -/
theorem exists_finitelyGenerated_factor [Algebra.FinitePresentation R A]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : Function.Surjective g) :
    ∃ (J : Ideal B) (hJ : J ≤ RingHom.ker g.toRingHom), J.FG ∧
      ∃ h : A →ₐ[R] B ⧸ J, (Ideal.Quotient.liftₐ J g (fun _ hb => hJ hb)).comp h = f := by
  classical
  obtain ⟨n, q, hq, hqfg⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  let l : MvPolynomial (Fin n) R →ₐ[R] B :=
    MvPolynomial.aeval (fun i => Function.surjInv hg (f (q (MvPolynomial.X i))))
  have hgl : g.comp l = f.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    change g (MvPolynomial.aeval _ (MvPolynomial.X i)) = f (q (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X]
    exact Function.rightInverse_surjInv hg _
  let J : Ideal B := (RingHom.ker q.toRingHom).map l.toRingHom
  have hJ : J ≤ RingHom.ker g.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change g (l a) = 0
    rw [show g (l a) = f (q a) from AlgHom.congr_fun hgl a]
    rw [show q a = 0 from ha, map_zero]
  have hkill : RingHom.ker q.toRingHom ≤
      RingHom.ker ((Ideal.Quotient.mkₐ R J).comp l).toRingHom := by
    intro a ha
    change Ideal.Quotient.mk J (l a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  let h : A →ₐ[R] B ⧸ J :=
    AlgHom.liftOfSurjective q hq ((Ideal.Quotient.mkₐ R J).comp l) hkill
  refine ⟨J, hJ, hqfg.map l.toRingHom, h, ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := hq a
  change Ideal.Quotient.liftₐ J g (fun _ hb => hJ hb) (h (q b)) = f (q b)
  rw [show h (q b) = Ideal.Quotient.mk J (l b) from
    AlgHom.liftOfSurjective_apply q hq ((Ideal.Quotient.mkₐ R J).comp l) hkill b]
  exact AlgHom.congr_fun hgl b

/-- Smooth algebras lift through every surjection whose kernel is a nil ideal. -/
theorem exists_lift [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : Function.Surjective g)
    (hnil : ∀ b ∈ RingHom.ker g.toRingHom, IsNilpotent b) :
    ∃ l : A →ₐ[R] B, g.comp l = f := by
  obtain ⟨J, hJ, hfg, h, hh⟩ := exists_finitelyGenerated_factor f g hg
  have hnilJ : IsNilpotent J := hfg.isNilpotent_iff_le_nilradical.mpr
    (fun b hb => hnil b (hJ hb))
  obtain ⟨l, hl⟩ := Algebra.FormallySmooth.exists_lift J hnilJ h
  refine ⟨l, ?_⟩
  have hcomp := congrArg (fun t => (Ideal.Quotient.liftₐ J g (fun _ hb => hJ hb)).comp t) hl
  exact hcomp.trans hh

/-- A chosen algebraic lift; its existence uses only finite presentation and smoothness. -/
def lift [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : Function.Surjective g)
    (hnil : ∀ b ∈ RingHom.ker g.toRingHom, IsNilpotent b) : A →ₐ[R] B :=
  (SmoothNilLifting.exists_lift f g hg hnil).choose

theorem comp_lift [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : Function.Surjective g)
    (hnil : ∀ b ∈ RingHom.ker g.toRingHom, IsNilpotent b) :
    g.comp (lift f g hg hnil) = f :=
  (SmoothNilLifting.exists_lift f g hg hnil).choose_spec

theorem lift_apply [Algebra.FinitePresentation R A] [Algebra.FormallySmooth R A]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hg : Function.Surjective g)
    (hnil : ∀ b ∈ RingHom.ker g.toRingHom, IsNilpotent b) (a : A) :
    g (lift f g hg hnil a) = f a :=
  AlgHom.congr_fun (comp_lift f g hg hnil) a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SmoothNil.SmoothNilLifting
