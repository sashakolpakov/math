import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ComparisonDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.PolarizedRigidityDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Polarized.IsoRigidity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.PicardFunctions

/-! # Pullback Comparison Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackComparisonDescent

noncomputable section

/-! Local comparisons with the actual pullback of a noetherian
universal family descend over arbitrary reduced test schemes. Regular
functions and Poincare normalization are supplied by the actual family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullback_pel_comparison_descends
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {Z S Y : Scheme.{0}} [IsLocallyNoetherian Z] [IsReduced S]
    {g N : ℕ} {δ : Fin g → ℕ} (A : PEL.Has.PolarizedActionData E g δ N Z)
    (hA : ∀ (V : Scheme.{0}) [IsReduced V] (t : V ⟶ Z)
      (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (A.polarized.pullback t) (A.polarized.pullback t)),
      e.abelian.hom = 𝟙 (A.polarized.abelian.pullback t).scheme)
    (f : S ⟶ Z) (B : PEL.Has.PolarizedActionData E g δ N S)
    (u : Y ⟶ S) [IsFinite u] [Etale u] [Surjective u]
    (e : PEL.Iso.PolarizedActionIso ((A.pullback f).pullback u) (B.pullback u)) :
    ∃ d : PEL.Iso.PolarizedActionIso (A.pullback f) B,
      (Over.pullback u).mapIso d.polarized.abelian = e.polarized.abelian ∧
      (Over.pullback u).mapIso d.polarized.dual = e.polarized.dual :=
  Reduced.ComparisonDescent.polarizedActionIso_descends_on_reduced_tests (A.pullback f) B u
    (fun V => AbelianModuli.ReferenceFamily.Pullback.PicardFunctions.pullbackFamily_product_app_isIso A.polarized.abelian f V ⊤)
    (fun V _ t => ⟨Polarized.IsoRigidity.polarizedIso_eq_of_source_rigidity
      (Reduced.PolarizedRigidityDescent.reduced_polarized_rigidity_pullback A.polarized hA f V t)⟩) e

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PullbackComparisonDescent
