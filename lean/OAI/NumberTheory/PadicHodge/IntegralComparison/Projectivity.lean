import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Projectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity.Construction

noncomputable section

/-!
# IntegralComparison: stable geometric projectivity predicate

Projectivity is a closed immersion into the actual finite-dimensional
projective space over the base. These definitions are shared by the
source statement and the developing comparison proof.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (k : Type*) [CommRing k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Projective n-space as the projective spectrum of the standard graded
polynomial ring in n + 1 variables. -/
def projectiveSpace (n : ℕ) : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)

/-- The canonical structure morphism of projective n-space over k. -/
def projectiveSpaceToSpec (n : ℕ) :
    projectiveSpace k n ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k 0)))

/-- The geometric projectivity predicate required by IntegralComparison. It asserts an
actual closed immersion into a finite-dimensional projective space over k. -/
def ProjectiveOver {X : Scheme} (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∃ (n : ℕ) (ι : X ⟶ projectiveSpace k n),
    IsClosedImmersion ι ∧ ι ≫ projectiveSpaceToSpec k n = f

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity.Construction
