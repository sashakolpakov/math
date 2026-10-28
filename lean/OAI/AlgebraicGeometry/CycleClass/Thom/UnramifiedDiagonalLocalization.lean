import OAI.AlgebraicGeometry.CycleClass.Thom.IdempotentIdealLocalization
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Unramified Diagonal Localization -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.UnramifiedDiagonalLocalization.Constructions

noncomputable section

/-! The relative diagonal ideal of a formally unramified algebra
vanishes after localization at a point on that diagonal. This is the
local algebra fact that removes the extra etale diagonal components. -/

open scoped TensorProduct

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FormallyUnramified R S]

theorem diagonal_idempotent : IsIdempotentElem (KaehlerDifferential.ideal R S) :=
  (Ideal.cotangent_subsingleton_iff _).mp (inferInstanceAs (Subsingleton Ω[S⁄R]))

variable [IsNoetherianRing (S ⊗[R] S)]

theorem local_diagonal_eq_bot (q : PrimeSpectrum S) :
    (KaehlerDifferential.ideal R S).map
      (algebraMap (S ⊗[R] S)
        (Localization.AtPrime (q.asIdeal.comap (Algebra.TensorProduct.lmul' R).toRingHom))) = ⊥ := by
  apply IdempotentIdealLocalization.Constructions.map_eq_bot (S ⊗[R] S)
    (KaehlerDifferential.ideal R S) (diagonal_idempotent R S)
    (PrimeSpectrum.comap (Algebra.TensorProduct.lmul' R).toRingHom q)
  intro a ha
  change Algebra.TensorProduct.lmul' R a ∈ q.asIdeal
  change Algebra.TensorProduct.lmul' R a = 0 at ha
  rw [ha]
  exact q.asIdeal.zero_mem

end

end OAI.AlgebraicGeometry.CycleClass.Thom.UnramifiedDiagonalLocalization.Constructions
