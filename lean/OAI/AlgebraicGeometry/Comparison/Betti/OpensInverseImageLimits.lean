import OAI.AlgebraicGeometry.Comparison.Betti.InfimumFunctorLimits
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Over

/-! # Opens Inverse Image Limits -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.OpensInverseImageLimits.RingedModules

noncomputable section

/-! Inverse image of actual open sets preserves products, pullbacks, and the induced slice-site coverage. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

theorem opensMap_prodComparison_isIso (U V : Opens Y) : IsIso (prodComparison (Opens.map f) U V) :=
  InfimumFunctorLimits.RingedModules.infFunctor_prodComparison_isIso (Opens.map f) (fun _ _ => rfl) U V

theorem opensMap_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (Opens.map f) :=
  InfimumFunctorLimits.RingedModules.infFunctor_preservesPullbacks (Opens.map f) (fun _ _ => rfl)

theorem opensMap_preservesOneHypercovers :
    (Opens.map f).PreservesOneHypercovers.{0} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  let : PreservesLimitsOfShape WalkingCospan (Opens.map f) := opensMap_preservesPullbacks f
  intro U E
  exact (Functor.PreservesOneHypercovers.of_coverPreserving (coverPreserving_opens_map f)) E

theorem opensMap_overPost_continuous (U : Opens Y) :
    (Over.post (X := U) (Opens.map f)).IsContinuous ((Opens.grothendieckTopology Y).over U)
      ((Opens.grothendieckTopology X).over ((Opens.map f).obj U)) := by
  let : (Opens.map f).PreservesOneHypercovers.{0}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) :=
    opensMap_preservesOneHypercovers f
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.OpensInverseImageLimits.RingedModules
