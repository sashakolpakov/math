import OAI.AlgebraicGeometry.Picard.PoincareBundle.RepresentedDualBaseChange
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.Extension
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MonoidalScalarPreservation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.ScalarClasses
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DualMapCongruence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GroupDescent

/-! # Dual Scalar -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualScalar

noncomputable section

/-! Over an arbitrary field, the dual of integer multiplication is integer multiplication, detected after algebraic closure. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.SharedRepresentation OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction

attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (n : ℕ)

/-- The scalar-duality equation holds over the original field, including imperfect fields. -/
theorem dual_scalar : DualMaps.representedDualMap
    (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)) (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)) ((𝟙 A.scheme) ^ n) =
      (𝟙 D.abelian.scheme) ^ n := by
  let s := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let F := Over.pullback s
  have : F.Faithful := Extension.pullback_faithful s
  let D' := D.pullback s
  let V := AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareVerticalMultiplication D'
  let H := AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction.originalPoincareHorizontalMultiplication D'
  let f' := AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap s ((𝟙 A.scheme) ^ n)
  have : IsMonHom f' := AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback.nativeBaseChangeMap_isMonHom s ((𝟙 A.scheme) ^ n)
  have hs : f' = (𝟙 (A.pullback s).scheme) ^ n := MonoidalScalarPreservation.map_scalar F A.scheme n
  have ht := MonoidalScalarPreservation.map_scalar F D.abelian.scheme n
  apply F.map_injective
  exact (RepresentedDualBaseChange.map_dual s ((𝟙 A.scheme) ^ n) D D).trans
    ((DualMapCongruence.representedDualMap_congr (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D'))
      (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D')) _ _ hs).trans
      ((Poincare.ScalarClasses.representedDualMap_scalar (Line.Comparison.Bundle.fromShared D'.poincare) H V
        (SharedRepresentation.representation (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D')) (SharedRepresentation.universalClass (Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D') _ _) n).trans ht.symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.DualScalar
