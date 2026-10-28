import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Colimits -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits.LargeZariskiColimits

noncomputable section

/-! # Small colimits for the native Zariski coefficient modules and sheaves -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

instance modules : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasColimitsOfSize.{u + 1, u + 1, 0, 0} R

instance sheaves : HasColimitsOfSize.{0, 0}
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) := by
  infer_instance

instance coproducts : HasCoproducts.{0}
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) :=
  fun J => (sheaves R X).has_colimits_of_shape (Discrete J)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits.LargeZariskiColimits
