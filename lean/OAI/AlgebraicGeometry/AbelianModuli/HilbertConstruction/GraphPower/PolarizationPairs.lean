import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.DiagonalPowerRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ClassPowers

/-! # Polarization Pairs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationPairs

noncomputable section

/-! Powers of the diagonal Poincare graph bundle recover doubled powers
of a symmetric polarization pairing, and hence of its dual-valued map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p q : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] [IsMonHom q]
variable (d : ℕ)
variable (hgraph : Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D p) ^ d =
  Line.Bundles.LineBundle.classOf (PoincareGraph.Bundles.poincareGraphBundle D q) ^ d)

include hgraph in
theorem graphPower_pairClass_eq (T : Over (Spec (.of K)))
    (hp : ∀ x y : T ⟶ A.scheme, D.poincarePairClass T (x ≫ p) y = D.poincarePairClass T (y ≫ p) x)
    (hq : ∀ x y : T ⟶ A.scheme, D.poincarePairClass T (x ≫ q) y = D.poincarePairClass T (y ≫ q) x)
    (x y : T ⟶ A.scheme) :
    Polarization.ClassPairing.polarizationPairClass D p T x y ^ (2 * d) = Polarization.ClassPairing.polarizationPairClass D q T x y ^ (2 * d) := by
  apply Bilinear.DiagonalPowerRecovery.symmetric_bilinear_pair_power_of_diagonal_power
    (Polarization.ClassPairing.polarizationPairClass D p T) (Polarization.ClassPairing.polarizationPairClass D q T) hp hq d
  intro z
  have h := congrArg (Line.Bundles.LineBundle.pullbackClassMonoidHom z.left) hgraph
  rw [map_pow, map_pow] at h
  change Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback z.left) ^ d =
    Line.Bundles.LineBundle.classOf ((PoincareGraph.Bundles.poincareGraphBundle D q).pullback z.left) ^ d at h
  rw [Polarization.ClassPairing.graphPullback_class_eq_pair, Polarization.ClassPairing.graphPullback_class_eq_pair] at h
  exact h

include hgraph in
theorem graphPower_determines_hom_power
    (hp : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x)
    (hq : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ q) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ q) x) :
    p ^ (2 * d) = q ^ (2 * d) := by
  apply D.poincareAt_pow_eq_of_classPower_eq A.scheme p q (2 * d)
  rw [Polarization.ClassPairing.poincareAt_class_eq_pair_projections D p, Polarization.ClassPairing.poincareAt_class_eq_pair_projections D q]
  exact graphPower_pairClass_eq D p q d hgraph (A.scheme ⊗ A.scheme) hp hq
    (fst A.scheme A.scheme) (snd A.scheme A.scheme)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PolarizationPairs
