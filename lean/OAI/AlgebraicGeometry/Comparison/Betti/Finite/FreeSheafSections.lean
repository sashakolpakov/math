import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.StdBasis

/-! # Free Sheaf Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.FreeSheafSections.RingedModules

noncomputable section

/-! A finite free module sheaf has genuinely free sections on every open. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J RingCat.{0}) (I : Type) [Finite I]

def finiteFreeSheafSectionIso (U : Cᵒᵖ) :
    (SheafOfModules.free (R := R) I).val.obj U ≅ ModuleCat.of (R.obj.obj U) (I → R.obj.obj U) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : HasFiniteBiproducts (SheafOfModules.{0} R) := HasFiniteBiproducts.of_hasFiniteProducts
  let A : I → SheafOfModules.{0} R := fun _ => SheafOfModules.unit R
  let e : SheafOfModules.free (R := R) I ≅ ∏ᶜ A :=
    (biproduct.isoCoproduct A).symm ≪≫ biproduct.isoProduct A
  exact (SheafOfModules.evaluation R U).mapIso e ≪≫
    PreservesProduct.iso (SheafOfModules.evaluation R U) A ≪≫
      ModuleCat.piIsoPi (fun i => (SheafOfModules.evaluation R U).obj (A i))

def finiteFreeSheafSectionBasis (U : Cᵒᵖ) :
    Module.Basis I (R.obj.obj U) ((SheafOfModules.free (R := R) I).val.obj U) := by
  let : Fintype I := Fintype.ofFinite I
  exact (Pi.basisFun (R.obj.obj U) I).map (finiteFreeSheafSectionIso J R I U).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.FreeSheafSections.RingedModules
