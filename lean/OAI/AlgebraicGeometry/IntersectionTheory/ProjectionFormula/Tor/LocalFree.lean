import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Symmetry
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedTorEuler
import Mathlib.RingTheory.LocalRing.Module

/-! # Local Free -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalFree

noncomputable section

/-! Over a local ring, vanishing of native Tor in degree one against
the residue field makes a finitely presented module free. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (M : ModuleCat.{u} R) [Module.FinitePresentation R M]

theorem of_residue_first
    (h : IsZero (((Tor (ModuleCat R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj M)) : Module.Free R M := by
  let S := IsolatedTorEuler.submoduleSequence R (ModuleCat.of R R) (maximalIdeal R)
  have hS := IsolatedTorEuler.submoduleSequence_shortExact R
    (ModuleCat.of R R) (maximalIdeal R)
  let : Projective S.X₂ := inferInstanceAs (Projective (ModuleCat.of R R))
  let e := OneFirst.kernelIso R M S hS
  have hz : IsZero (ModuleCat.of R (((maximalIdeal R).subtype.rTensor M).ker)) :=
    h.of_iso e.symm
  let := ModuleCat.subsingleton_of_isZero hz
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

theorem of_residue_second
    (h : IsZero (((Tor (ModuleCat R) 1).obj M).obj
      (ModuleCat.of R (ResidueField R)))) : Module.Free R M :=
  of_residue_first R M (h.of_iso
    (Symmetry.iso R M (ModuleCat.of R (ResidueField R)) 1).symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.LocalFree
