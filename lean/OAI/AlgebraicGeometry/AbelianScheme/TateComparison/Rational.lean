import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Add
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Rational -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

noncomputable section

/-! Rational Tate spaces and the intrinsic lattices associated to actual
isogenies. The lattice is a preimage under the induced rational Tate map;
no inverse map or comparison with abstract Hecke flags is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

universe u

variable {S : Scheme.{u}} (A : Over S) [GrpObj A] [IsCommMonObj A]
  (T : Over S) (q : ℕ) [Fact q.Prime]

abbrev rationalTateModule := ℚ_[q] ⊗[ℤ_[q]] Add.schemeTateModule A T q

/-- The actual integral Tate image inside its scalar extension. -/
def integralTateImage : Submodule ℤ_[q] (rationalTateModule A T q) :=
  (TensorProduct.mk ℤ_[q] ℚ_[q] (Add.schemeTateModule A T q) 1).range

variable {A T q} {B : Over S} [GrpObj B] [IsCommMonObj B]

/-- Scalar extension of the map induced by a genuine group-scheme morphism. -/
def rationalTateMap (f : A ⟶ B) [IsMonHom f] :
    rationalTateModule A T q →ₗ[ℚ_[q]] rationalTateModule B T q :=
  (Add.schemeTateMap A T q f).baseChange ℚ_[q]

/-- For an isogeny, this is the overlattice in the source rational Tate
space corresponding to the target's integral Tate module. -/
def isogenyTatePreimage (f : A ⟶ B) [IsMonHom f] :
    Submodule ℤ_[q] (rationalTateModule A T q) :=
  (integralTateImage B T q).comap ((rationalTateMap (T := T) (q := q) f).restrictScalars ℤ_[q])

abbrev SplitTateSpace (s q : ℕ) [Fact q.Prime] := (Fin s × Bool) → Fin 3 → ℚ_[q]

/-- A split frame is an actual linear coordinate isomorphism, rather than
an assumed identification of flags. Its arithmetic conditions are separate. -/
abbrev SplitTateFrame (s : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (T : Over S) (q : ℕ) [Fact q.Prime] :=
  rationalTateModule A T q ≃ₗ[ℚ_[q]] SplitTateSpace s q

/-- Project the intrinsic target overlattice onto one chosen or opposite
coordinate block. All maps here come from the frame and the actual isogeny. -/
def framedTateLattice {s : ℕ} (e : SplitTateFrame s A T q)
    (f : A ⟶ B) [IsMonHom f] (v : Fin s × Bool) : Submodule ℤ_[q] (Fin 3 → ℚ_[q]) :=
  ((isogenyTatePreimage (T := T) (q := q) f).map
    (e.toLinearMap.restrictScalars ℤ_[q])).map
      ((LinearMap.proj v : SplitTateSpace s q →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q])).restrictScalars ℤ_[q])

def framedIntegralTateImage {s : ℕ} (e : SplitTateFrame s A T q) :
    Submodule ℤ_[q] (SplitTateSpace s q) :=
  (integralTateImage A T q).map (e.toLinearMap.restrictScalars ℤ_[q])

/-- Equivariance of a genuine Tate coordinate frame for the integral action. -/
def IsSplitActionFrame {R : Type u} [CommRing R] {g N s : ℕ}
    (F : PEL.PELFamilyData R g N S) (T : Over S) (q : ℕ) [Fact q.Prime]
    (χ : Fin s × Bool → R →+* ℤ_[q])
    (e : SplitTateFrame s F.abelian.scheme T q) : Prop :=
  ∀ (a : R) (z : rationalTateModule F.abelian.scheme T q)
    (v : Fin s × Bool) (i : Fin 3),
    e (rationalTateMap (T := T) (q := q)
      (End.endSchemeMap F.abelian.scheme (F.action a)) z) v i =
      (χ v a : ℚ_[q]) * e z v i

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational
