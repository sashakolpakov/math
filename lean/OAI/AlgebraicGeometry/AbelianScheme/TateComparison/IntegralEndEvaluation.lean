import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseEndExt

/-! # Integral End Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Additive evaluation of actual endomorphisms and of differences of
actual scheme-map values. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def IntegralEndEvaluation.pointDifferenceEvaluation {S : Scheme} {X T A : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : T ⟶ X) : Additive (X ⟶ A) →+ Additive (T ⟶ A) :=
  let ex : Additive (X ⟶ A) →+ Additive (T ⟶ A) := ((yonedaGrpObj A).map x.op).hom.toAdditive
  let ey : Additive (X ⟶ A) →+ Additive (T ⟶ A) := ((yonedaGrpObj A).map y.op).hom.toAdditive
  ex - ey

theorem IntegralEndEvaluation.pointDifferenceEvaluation_apply {S : Scheme} {X T A : Over S} [GrpObj A] [IsCommMonObj A]
    (x y : T ⟶ X) (f : X ⟶ A) :
    IntegralEndEvaluation.pointDifferenceEvaluation x y (Additive.ofMul f) = Additive.ofMul ((x ≫ f) / (y ≫ f)) := rfl

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)

def Data.SphericalPELAlbaneseData.endPointEvaluation {T : Over (Spec (.of K))} (z : Additive (T ⟶ D.albaneseGroup.X)) :
    D.EndK →+ Additive (T ⟶ D.albaneseGroup.X) where
  toFun a := D.endPoint a z
  map_zero' := by rw [D.endPoint_eq_app]; rfl
  map_add' a b := D.endPoint_add a b z

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
