import OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafLocalExactness
import Mathlib.CategoryTheory.Sites.Limits

/-! # Coproducts -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coproducts.IntrinsicCechCoproducts

/-! Small coproducts in the native category of module sheaves. -/

open _root_.CategoryTheory Limits

theorem hasCoproducts (R : Type) [CommRing R] (X : TopCat.{0}) :
    HasCoproducts.{0} (TopCat.Sheaf (ModuleCat.{0} R) X) := inferInstance

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Coproducts.IntrinsicCechCoproducts
