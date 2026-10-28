import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CoefficientMap
import OAI.NumberTheory.ArithmeticGroups.Lattices.ConnectedBaseChange

/-! # Char Zero Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent.Construction

noncomputable section

/-! Tangent equations describe the concrete infinitesimal stabilizer
over every characteristic-zero base field. -/

open scoped Classical

theorem mem_infinitesimalStabilizer_iff_tangent
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Matrix (Fin n) (Fin n) k) :
    A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G ↔
      ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G,
        Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Infinitesimal.Action.Construction.rightInfinitesimal A p) = 0 := by
  constructor
  · intro hA p hp
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA p hp k (RingHom.id k)
      (1 : G.RationalPoints)
  · intro ht
    have hle := (Infinitesimal.CoefficientMap.Construction.vanishingIdeal_le_identityTangentIdeal_iff G A).mpr ht
    have hmap :
        VanishingIdeal.Construction.coordinateVanishingIdeal (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k (AlgebraicClosure k))) ≤
          Infinitesimal.CoefficientMap.Construction.identityTangentIdeal (A.map (algebraMap k (AlgebraicClosure k))) := by
      rw [GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG]
      exact (Ideal.map_mono hle).trans (Infinitesimal.CoefficientMap.Construction.identityTangentIdeal_coefficient_map _ A)
    have hA := (TangentIdentity.Construction.mem_infinitesimalStabilizer_iff_at_identity _ _).mpr
      ((Infinitesimal.CoefficientMap.Construction.vanishingIdeal_le_identityTangentIdeal_iff _ _).mp hmap)
    apply (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mpr
    intro p hp
    rw [← GeometricIrreducibility.Construction.geometricVanishingIdeal_comap G, Ideal.mem_comap,
      ConnectedBaseChange.Construction.geometricVanishingIdeal_eq_baseChange_ideal, ← Infinitesimal.CoefficientMap.Construction.rightInfinitesimal_coefficient_map]
    exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer _ _).mp hA _
      (BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal G _ hp)

theorem infinitesimalStabilizer_coefficient_map
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    A.map (algebraMap k K) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G (algebraMap k K)) := by
  let : CharZero K := Algebra.charZero_of_charZero k K
  have ht := (mem_infinitesimalStabilizer_iff_tangent G hG A).mp hA
  have hle := (Infinitesimal.CoefficientMap.Construction.vanishingIdeal_le_identityTangentIdeal_iff G A).mpr ht
  apply (mem_infinitesimalStabilizer_iff_tangent _ (ConnectedBaseChange.Construction.geometrically_connected_baseChange G hG) _).mpr
  apply (Infinitesimal.CoefficientMap.Construction.vanishingIdeal_le_identityTangentIdeal_iff _ _).mp
  rw [GeneralVanishingBaseChange.Construction.vanishingIdeal_charZero_baseChange G hG]
  exact (Ideal.map_mono hle).trans (Infinitesimal.CoefficientMap.Construction.identityTangentIdeal_coefficient_map _ A)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent.Construction
