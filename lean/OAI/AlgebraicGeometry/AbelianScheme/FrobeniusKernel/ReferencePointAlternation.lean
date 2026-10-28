import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferenceFieldAlternation
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointFieldPairing

/-! # Reference Point Alternation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAlternation.Construction

noncomputable section

/-! The canonical point pairing is alternating and skew on the original
source torsion functor, over every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem bicharacter_skew_of_alternating {G W : Type*} [CommGroup G] [CommGroup W]
    (b : G →* G →* W) (halt : ∀ x, b x x = 1) (x y : G) :
    b y x = (b x y)⁻¹ := by
  have h : b y x * b x y = 1 := by
    have ht := halt (x * y)
    simpa only [map_mul, MonoidHom.mul_apply, halt x, halt y, one_mul, mul_one] using ht
  exact (mul_eq_one_iff_eq_inv).mp h

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))

theorem originalPointBicharacter_alternating (x : (A.abelian.torsionFunctor n).obj (.op T)) :
    ReferencePointBicharacter.Construction.originalPointBicharacter A n hn T x x = 1 :=
  (ReferencePointBicharacter.Construction.originalPointBicharacter_value A n hn T x x).trans
    ((ReferencePointFieldPairing.Construction.originalPointPairing_field A n hn T x x).symm.trans
      (ReferenceFieldAlternation.Construction.originalFieldPolarizationPairing_alternating A.dual A.polarization n hn
        (ReferencePointFieldPairing.Construction.originalPointToFieldNative A n T x)))

theorem originalPointBicharacter_skew (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    ReferencePointBicharacter.Construction.originalPointBicharacter A n hn T y x = (ReferencePointBicharacter.Construction.originalPointBicharacter A n hn T x y)⁻¹ :=
  bicharacter_skew_of_alternating (ReferencePointBicharacter.Construction.originalPointBicharacter A n hn T)
    (originalPointBicharacter_alternating A n hn T) x y

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAlternation.Construction
