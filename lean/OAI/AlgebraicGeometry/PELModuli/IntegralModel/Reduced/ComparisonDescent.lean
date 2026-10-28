import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedIsoDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Iso

/-! # Comparison Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ComparisonDescent

noncomputable section

/-! The integral action equations descend with the actual polarized
family comparison. Rigidity is required only on reduced base tests. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem polarizedActionIso_descends_on_reduced_tests
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {S Y : Scheme.{0}} [IsReduced S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PEL.Has.PolarizedActionData E g δ N S) (u : Y ⟶ S)
    [IsFinite u] [Etale u] [Surjective u]
    (hΓ : ∀ V : Over S, IsIso (fst V A.polarized.abelian.scheme).left.appTop)
    (hr : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ S),
      Subsingleton (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.polarized.pullback t) (B.polarized.pullback t)))
    (e : PEL.Iso.PolarizedActionIso (A.pullback u) (B.pullback u)) :
    ∃ d : PEL.Iso.PolarizedActionIso A B,
      (Over.pullback u).mapIso d.polarized.abelian = e.polarized.abelian ∧
      (Over.pullback u).mapIso d.polarized.dual = e.polarized.dual := by
  obtain ⟨d, hA, hD⟩ := PolarizedIsoDescent.polarizedIso_descends_on_reduced_tests
    A.polarized B.polarized u hΓ hr e.polarized
  have ha : (Over.pullback u).map d.abelian.hom = e.polarized.abelian.hom := congrArg Iso.hom hA
  let c : PEL.Iso.PolarizedActionIso A B := {
    polarized := d
    action r := by
      apply (Over.pullback u).map_injective
      rw [(Over.pullback u).map_comp, (Over.pullback u).map_comp, ha]
      exact e.action r }
  exact ⟨c, hA, hD⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ComparisonDescent
