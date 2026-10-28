import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

/-! # Label Enumeration -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The fixed enumeration of ordered full-level labels. -/

variable {g n : ℕ} [NeZero n]

def PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration : Fin (n ^ (2 * g)) ≃ Multiplicative (Fin (2 * g) → ZMod n) :=
  ((Fintype.equivFin (Multiplicative (Fin (2 * g) → ZMod n))).trans (finCongr (by simp))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
