import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationEuler
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-! # Sequence Module -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule

noncomputable section

/-! The native quotient by a regular sequence has its actual support,
annihilator action, and projective-dimension bound equal to the length
of the sequence. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory

universe u

variable (R : Type u) [CommRing R]

def quotient (rs : List R) : ModuleCat.{u} R := .of R (R ⧸ Ideal.ofList rs)

instance (rs : List R) : Module.Finite R (quotient R rs) := by unfold quotient; infer_instance

theorem support (rs : List R) :
    Module.support R (quotient R rs) = PrimeSpectrum.zeroLocus (Ideal.ofList rs) := by
  change Module.support R (R ⧸ Ideal.ofList rs) = _
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

theorem killed (rs : List R) (r : R) (hr : r ∈ rs) (m : quotient R rs) : r • m = 0 := by
  change Ideal.Quotient.mk (Ideal.ofList rs) r * (show R ⧸ Ideal.ofList rs from m) = 0
  rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (show r ∈ Ideal.ofList rs from Ideal.subset_span hr), zero_mul]

theorem projectiveDimension [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (hr : RingTheory.Sequence.IsRegular R rs) :
    HasProjectiveDimensionLE (quotient R rs) rs.length := by
  have hp : CategoryTheory.projectiveDimension (ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs))) = rs.length :=
    ModuleCat.projectiveDimension_quotient_eq_length rs hr
  have he := CategoryTheory.projectiveDimension_eq_of_iso (Shrink.linearEquiv R (R ⧸ Ideal.ofList rs)).toModuleIso
  exact (projectiveDimension_le_iff (quotient R rs) rs.length).mp (he.symm.trans hp).le

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceModule
