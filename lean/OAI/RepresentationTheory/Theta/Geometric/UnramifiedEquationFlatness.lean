import OAI.RepresentationTheory.Theta.Geometric.CotangentRelationBound
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Etale.Basic

/-! # Unramified Equation Flatness -/

namespace OAI.RepresentationTheory.Theta.Geometric.UnramifiedEquationFlatness

noncomputable section

/-! A sufficiently small system of equations in a smooth ambient
presentation gives a formally etale quotient. Over a Noetherian flat
ambient algebra the same quotient is flat. -/

open KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] (P : Algebra.Extension R S)
    [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    [Algebra.FormallyUnramified R S]

include P in
theorem formallyEtale_of_unramified_ambient_rank {n : ℕ} (r : Fin n → P.Ring)
    (hr : Ideal.span (Set.range r) = P.ker)
    (hn : n ≤ Module.finrank P.Ring Ω[P.Ring⁄R]) : Algebra.FormallyEtale R S := by
  have : Algebra.FormallySmooth R S := CotangentRelationBound.formallySmooth_of_unramified_ambient_rank P r hr hn
  exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth

include P in
theorem flat_of_unramified_ambient_rank [Module.Flat R P.Ring] [IsNoetherianRing P.Ring]
    {n : ℕ} (r : Fin n → P.Ring) (hr : Ideal.span (Set.range r) = P.ker)
    (hn : n ≤ Module.finrank P.Ring Ω[P.Ring⁄R]) : Module.Flat R S := by
  have : Algebra.FormallySmooth R S := CotangentRelationBound.formallySmooth_of_unramified_ambient_rank P r hr hn
  exact Algebra.FormallySmooth.flat_of_algHom_of_isNoetherianRing
    (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective

end

end OAI.RepresentationTheory.Theta.Geometric.UnramifiedEquationFlatness
