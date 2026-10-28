import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Sheaf Coproducts -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts

/-! An explicit small-coproduct interface for module sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
theorem hasCoproducts {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
    (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)] :
    HasCoproducts.{0} (Sheaf J (ModuleCat.{w} R)) := inferInstance

end OAI.NumberTheory.PadicHodge.GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts
