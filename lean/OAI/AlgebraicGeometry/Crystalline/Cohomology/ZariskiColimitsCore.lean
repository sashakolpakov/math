import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Zariski Colimits Core -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiColimitsCore.ZariskiColimits

noncomputable section

/-! # Small colimits for the native Zariski coefficient modules and sheaves -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (X : Scheme.{u})

instance modules : HasColimitsOfSize.{0, 0} (ModuleCat.{u} R) :=
  ModuleCat.hasColimitsOfSize.{u, u, 0, 0} R

instance sheaves : HasColimitsOfSize.{0, 0}
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) := by
  infer_instance

instance coproducts : HasCoproducts.{0}
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  fun J => (sheaves R X).has_colimits_of_shape (Discrete J)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ZariskiColimitsCore.ZariskiColimits
