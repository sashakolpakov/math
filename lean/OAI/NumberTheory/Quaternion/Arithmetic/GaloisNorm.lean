import OAI.NumberTheory.Quaternion.Arithmetic.GaloisPoints
import OAI.NumberTheory.Quaternion.Arithmetic.CommutingOrbitNorm

/-! # Galois Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GaloisNorm

noncomputable section

/-! A commuting Galois orbit of actual algebraic-group points has a
norm product defined over the base field. -/

open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra F K] {n : ℕ}

def galoisPointsAction (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    (K ≃ₐ[F] K) →* Monoid.End (G.Points (algebraMap F K)) where
  toFun := GaloisPoints.galoisPointsHom G
  map_one' := GaloisPoints.galoisPointsHom_one G
  map_mul' := GaloisPoints.galoisPointsHom_mul G

variable [FiniteDimensional F K]

def galoisPointNorm (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.Points (algebraMap F K))
    (hc : ∀ σ τ : K ≃ₐ[F] K, Commute (GaloisPoints.galoisPointsHom G σ g) (GaloisPoints.galoisPointsHom G τ g)) :
    G.Points (algebraMap F K) := CommutingOrbitNorm.commutingOrbitNorm (galoisPointsAction G) g hc

theorem galoisPointNorm_fixed (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.Points (algebraMap F K))
    (hc : ∀ σ τ : K ≃ₐ[F] K, Commute (GaloisPoints.galoisPointsHom G σ g) (GaloisPoints.galoisPointsHom G τ g))
    (σ : K ≃ₐ[F] K) : GaloisPoints.galoisPointsHom G σ (galoisPointNorm G g hc) = galoisPointNorm G g hc :=
  CommutingOrbitNorm.commutingOrbitNorm_fixed (galoisPointsAction G) g hc σ

theorem galoisPointNorm_descends [IsGalois F K]
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (g : G.Points (algebraMap F K))
    (hc : ∀ σ τ : K ≃ₐ[F] K, Commute (GaloisPoints.galoisPointsHom G σ g) (GaloisPoints.galoisPointsHom G τ g)) :
    ∃ a : G.RationalPoints, G.map (RingHom.id F) (algebraMap F K) a = galoisPointNorm G g hc :=
  GaloisPoints.galois_fixed_point_descends G _ (galoisPointNorm_fixed G g hc)

end

end OAI.NumberTheory.Quaternion.Arithmetic.GaloisNorm
