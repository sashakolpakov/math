import Mathlib.AlgebraicGeometry.Noetherian

/-! # Immersion Noetherian -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian.BundleCycles

/-! # LineBundleCycles: every open subscheme of a Noetherian scheme is Noetherian -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem openImmersion_isNoetherian {U X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : U ⟶ X) [IsOpenImmersion i] : AlgebraicGeometry.IsNoetherian U := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian i
  have : NoetherianSpace U := i.isOpenEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.ImmersionNoetherian.BundleCycles
