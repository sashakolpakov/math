import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseEndExt
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalEndArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseProduct

/-! # Albanese Rational End -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! The actual product Albanese has a torsion-free integral endomorphism
ring and a faithful rationalization, with positive denominator clearings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

include hg in
theorem Data.SphericalPELAlbaneseData.albaneseGroup_geometricallyConnected : GeometricallyConnected D.albaneseGroup.X.hom := by
  have : GeometricallyConnected (Products.componentProduct D.components.A).X.hom :=
    (HodgeConjecture.HeckeCycles.AlbaneseProduct.CM.component_product_geometry D.components.A hg.abelianGeometry).2.2
  exact inferInstanceAs (GeometricallyConnected
    (pullback.snd (Products.componentProduct D.components.A).X.hom D.generic))

include hg in
theorem Data.SphericalPELAlbaneseData.albaneseEnd_isAddTorsionFree : IsAddTorsionFree D.EndK := by
  have : IsProper D.albaneseGroup.X.hom := (CentralAction.AlbaneseExt.Construction.albaneseGroup_smooth_proper D hg).2
  have : GeometricallyConnected D.albaneseGroup.X.hom := D.albaneseGroup_geometricallyConnected hg
  have : ConnectedSpace D.albaneseGroup.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.albaneseGroup.X.hom
  exact EndTorsionFree.integralEnd_isAddTorsionFree D.albaneseGroup.X

include hg in
theorem Data.SphericalPELAlbaneseData.toRational_injective : Function.Injective D.toRational := by
  have := D.albaneseEnd_isAddTorsionFree hg
  exact RationalEndArithmetic.endToRational_injective D.albaneseGroup.X

theorem Data.SphericalPELAlbaneseData.endQ_positive_denominator (x : D.EndQ) :
    ∃ (n : ℕ), 0 < n ∧ ∃ a : D.EndK, n • x = D.toRational a :=
  RationalEndArithmetic.rationalEnd_positive_denominator D.albaneseGroup.X x

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
