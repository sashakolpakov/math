import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelIsoBaseOverlap
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RecoveredPolarizedIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ActionDescent

/-! # Polarized Iso Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedIsoDescent

noncomputable section

/-! A local polarized comparison descends effectively through a finite
etale cover using rigidity only on reduced base test schemes. Both actual
group isomorphisms and the complete polarized data are recovered. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem polarizedIso_descends_on_reduced_tests
    {S Y : Scheme.{0}} [IsReduced S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    [IsFinite u] [Etale u] [Surjective u]
    (hΓ : ∀ V : Over S, IsIso (fst V A.abelian.scheme).left.appTop)
    (hr : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ S),
      Subsingleton (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback t) (B.pullback t)))
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.pullback u) (B.pullback u)) :
    ∃ d : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A B, (Over.pullback u).mapIso d.abelian = e.abelian ∧
      (Over.pullback u).mapIso d.dual = e.dual := by
  obtain ⟨hah, hai, hdh, hdi⟩ := LevelIsoBaseOverlap.levelIso_compatible_of_reduced_rigidity A B u e hr
  obtain ⟨qA, hA, _⟩ := AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.exists_unique_iso u e.abelian hah hai
  obtain ⟨qD, hD, _⟩ := AbelianModuli.ReferenceFamily.EtaleDescentLocal.EtaleDescent.exists_unique_iso u e.dual hdh hdi
  have : IsMonHom ((Over.pullback u).map qA.hom) := by
    have h : (Over.pullback u).map qA.hom = e.abelian.hom := congrArg Iso.hom hA
    rw [h]
    exact e.abelianGroup
  have : IsMonHom qA.hom := ActionDescent.isMonHom_of_faithful_map (Over.pullback u) qA.hom
  have : IsMonHom ((Over.pullback u).map qD.hom) := by
    have h : (Over.pullback u).map qD.hom = e.dual.hom := congrArg Iso.hom hD
    rw [h]
    exact e.dualGroup
  have : IsMonHom qD.hom := ActionDescent.isMonHom_of_faithful_map (Over.pullback u) qD.hom
  exact ⟨RecoveredPolarizedIso.recoveredPolarizedIso A B u e qA qD hA hD hΓ, hA, hD⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedIsoDescent
