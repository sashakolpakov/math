import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComponent

/-! # Bicomplex Composite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComposite.BicomplexCompositeHomology

noncomputable section

/-! Compare a composite of original total maps with a single
bicomplex total map through the relevant diagonal components. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L M : HomologicalComplex₂ A (.up ℕ) (.up ℕ)}
  [HasCoproducts.{0} A]

theorem homology (a : K ⟶ L) (b : L ⟶ M) (c : K ⟶ M) (i : ℕ)
    (h : ∀ q r, q + r = i → (a.f q).f r ≫ (b.f q).f r = (c.f q).f r) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map a (.up ℕ) ≫ HomologicalComplex₂.total.map b (.up ℕ)) i =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map c (.up ℕ)) i := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  have ht : HomologicalComplex₂.total.map a (.up ℕ) ≫ HomologicalComplex₂.total.map b (.up ℕ) =
      HomologicalComplex₂.total.map (a ≫ b) (.up ℕ) := (T.map_comp a b).symm
  exact (congrArg (fun f => HomologicalComplex.homologyMap f i) ht).trans
    (BicomplexComponent.BicomplexComponentHomology.homology (a ≫ b) c i h)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComposite.BicomplexCompositeHomology
