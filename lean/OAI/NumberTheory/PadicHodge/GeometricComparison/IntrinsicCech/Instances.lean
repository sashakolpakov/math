import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Functor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Sites.Limits

/-! # Instances -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Instances.IntrinsicCechInstances

/-! Explicit native category instances used by the finite-diagonal Čech total construction. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Scheme.{0})

theorem hasCoproducts : HasCoproducts.{0} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} R)) :=
  Coproducts.IntrinsicCechCoproducts.hasCoproducts R (TopCat.of X)

theorem additive {ι : Type} (U : ι → X.Opens) : (Functor.IntrinsicCechFunctor.sheafFunctor R X U).Additive :=
  Functor.IntrinsicCechFunctor.sheaf_additive R X U

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Instances.IntrinsicCechInstances
