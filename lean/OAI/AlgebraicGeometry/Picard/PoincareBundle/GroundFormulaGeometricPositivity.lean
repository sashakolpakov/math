import OAI.AlgebraicGeometry.Picard.PoincareBundle.PositiveFormulaAffineSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange

/-! # Ground Formula Geometric Positivity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GroundFormulaGeometricPositivity

noncomputable section

/-! A normalized ample Poincare formula over the original field gives positivity on every geometric fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange

variable {k : Type u} [Field k] {a : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))}
  (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme)

/-- Actual affine base change transports the inducing line and tensor formula to each geometric point. -/
theorem positiveOnGeometricFiber
    (hp : AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left))
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Spec (.of k)) :
    AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s := by
  let B := (A.pullback s).scheme
  let q : B.left ⟶ A.scheme.left := pullback.fst A.scheme.hom s
  let r := PoincareBundle.Field.ProductBaseChange.productMap s A.scheme
  have : IsAffineHom s := isAffineHom_of_isAffine _
  have : IsAffineHom q := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.scheme.hom s).flip (inferInstance : IsAffineHom s)
  let e : (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).sheaf ≅
      (Scheme.Modules.pullback r).obj (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left).sheaf :=
    (Scheme.Modules.pullbackCongr (PoincareBundle.Field.ProductBaseChange.poincare_square s D p)).app D.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackComp r (p ⊗ₘ 𝟙 A.scheme).left).symm.app D.poincare.sheaf
  exact PositiveFormulaAffineSquare.positive A.scheme B q r (PoincareBundle.Field.ProductBaseChange.first s A.scheme) (PoincareBundle.Field.ProductBaseChange.second s A.scheme)
    (PoincareBundle.Field.ProductBaseChange.multiplication s A.scheme) (D.poincare.pullback (p ⊗ₘ 𝟙 A.scheme).left)
    (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) e hp

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GroundFormulaGeometricPositivity
