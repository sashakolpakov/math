import OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

/-! # Coprime Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimePairing

/-! Bilinear pairings vanish between factors killed by coprime integers. -/

universe u v w

variable {A : Type u} {B : Type v} {V : Type w} [Group A] [Group B] [CommGroup V]

/-- Coprime torsion forces a bilinear pairing value to be the identity. -/
theorem value_eq_one (e : A →* B →* V) (n m : ℕ) (hnm : n.Coprime m)
    (x : A) (y : B) (hx : x ^ n = 1) (hy : y ^ m = 1) : e x y = 1 := by
  apply CoprimeKernels.eq_one_of_coprime_powers n m hnm
  · change (e.flip y x) ^ n = 1
    rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimePairing
