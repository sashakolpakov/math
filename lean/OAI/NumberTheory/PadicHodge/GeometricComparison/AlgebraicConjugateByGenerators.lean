import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Algebraic Conjugate By Generators -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicConjugateByGenerators.CommAlgebraicConjugateByGenerators

noncomputable section

/-! Conjugated algebra maps are determined by their values on a surjective presentation. -/

open _root_.CategoryTheory

universe u v a b t
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{v} R}
  {F : Type a} [CommRing F] {G : Type b} [CommRing G] {T : Type t} [CommRing T]

theorem on_generator (c d : A ⟶ B) (i : A →+* F) (r : F →+* G) (o : G →+* B)
    (s : T →+* A) (h : c.hom.toRingHom = o.comp (r.comp i)) (k : T → G)
    (hk : ∀ a, r (i (s a)) = k a) (hd : ∀ a, o (k a) = d.hom.toRingHom (s a)) (a : T) :
    c.hom.toRingHom (s a) = d.hom.toRingHom (s a) :=
  (RingHom.congr_fun h (s a)).trans ((congrArg o (hk a)).trans (hd a))

theorem eq (c d : A ⟶ B) (i : A →+* F) (r : F →+* G) (o : G →+* B)
    (s : T →+* A) (hs : Function.Surjective s)
    (h : c.hom.toRingHom = o.comp (r.comp i)) (k : T → G)
    (hk : ∀ a, r (i (s a)) = k a)
    (hd : ∀ a, o (k a) = d.hom.toRingHom (s a)) : c = d := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := hs x
  exact (RingHom.congr_fun h (s a)).trans ((congrArg o (hk a)).trans (hd a))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicConjugateByGenerators.CommAlgebraicConjugateByGenerators
