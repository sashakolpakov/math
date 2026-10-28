import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Tensor Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorProducts.FiniteTensorProducts

noncomputable section

/-! Extension of scalars commutes with finite products of modules. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
instance extend_additive :
    (ModuleCat.extendScalars f : ModuleCat.{u} R ⥤ ModuleCat.{u} S).Additive := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{u} S := ModuleCat.extendScalars f
  have : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj f).isLeftAdjoint
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

variable {I : Type u} [Finite I] (P : I → ModuleCat.{u} R)

theorem comparison_isIso : IsIso (piComparison (ModuleCat.extendScalars f) P) := by
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TensorProducts.FiniteTensorProducts
