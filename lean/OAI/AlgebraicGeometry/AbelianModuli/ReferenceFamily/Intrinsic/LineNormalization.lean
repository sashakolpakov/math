import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Line Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LineNormalization

noncomputable section

/-! Normalize an actual line bundle at the abelian identity. Native
recovery of an already normalized line survives this operation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

variable {S : Scheme.{0}} {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (T : Over S)
    (L : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left)

def normalizedNativeLine : HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A.scheme).left :=
  Quotient.out (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass A T (HilbertConstruction.Line.Bundles.LineBundle.classOf L))

theorem normalizedNativeLine_class :
    HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedNativeLine A T L) = PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass A T (HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
  Quotient.out_eq _

theorem normalizedNativeLine_zero : Nonempty
    ((HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (normalizedNativeLine A T L)).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule T.left) := by
  have h : HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left (normalizedNativeLine A T L)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.Line.Bundles.LineBundle.trivial T.left) :=
    (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.PoincareNormalization.familyZero A T).left)
    (normalizedNativeLine_class A T L)).trans (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_zero A T (HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  exact Quotient.exact h

theorem normalizedNativeLine_recovery {V : Over S} (q : V ⟶ T)
    (J : HilbertConstruction.Line.Bundles.LineBundle (V ⊗ A.scheme).left)
    (eJ : (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left J).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule V.left)
    (hJ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf L) = HilbertConstruction.Line.Bundles.LineBundle.classOf J) :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (normalizedNativeLine A T L)) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf J := by
  have hz : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A V).left (HilbertConstruction.Line.Bundles.LineBundle.classOf J) = 1 :=
    Quotient.sound ⟨eJ⟩
  exact (congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ▷ A.scheme).left) (normalizedNativeLine_class A T L)).trans
    ((PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_naturality A q (HilbertConstruction.Line.Bundles.LineBundle.classOf L)).trans
      ((congrArg (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass A V) hJ).trans (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self A V (HilbertConstruction.Line.Bundles.LineBundle.classOf J) hz)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LineNormalization
