import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TestLineTriviality
import OAI.RepresentationTheory.Theta.Geometric.ParameterizedPicardClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairClass
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.PairNaturality

/-! # Poincare Dual Pair Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareDualPairCoordinates

noncomputable section

/-! On the original dual-number product, Poincare evaluation of a
parameter against the variable point is its actual parameter line
class. Evaluation of two base-only points is proved trivial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Foundations.Scheme.ProjectiveSpace.complexBase) (D : HilbertConstruction.Dual.Data.DualAbelianData A)

theorem poincareParameterLineClass_eq_pair (t : LieRanks.dualNumberTest ℂ ⟶ D.abelian.scheme) :
    RepresentationTheory.Theta.Geometric.ParameterizedPicardClass.parameterLineClass D.poincare t = D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ A.scheme)
      (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (snd (LieRanks.dualNumberTest ℂ) A.scheme) := by
  have hj : lift (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (snd (LieRanks.dualNumberTest ℂ) A.scheme) =
      t ⊗ₘ 𝟙 A.scheme := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have h : D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ A.scheme)
    (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (snd (LieRanks.dualNumberTest ℂ) A.scheme) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t)
        (snd (LieRanks.dualNumberTest ℂ) A.scheme)).left (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare) :=
    Quotient.sound ⟨D.poincarePairDirectIso
      (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (snd (LieRanks.dualNumberTest ℂ) A.scheme)⟩
  rw [hj] at h
  exact h.symm

theorem poincareDualBasePair_trivial
    (t : LieRanks.dualNumberTest ℂ ⟶ D.abelian.scheme) (s : LieRanks.dualNumberTest ℂ ⟶ A.scheme) :
    D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ A.scheme)
      (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ s) = 1 := by
  have h₀ : HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincarePair t s) = 1 :=
    Quotient.sound (Dual.TestLineTriviality.dualNumberTestLine_trivial (D.poincarePair t s))
  have h : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst (LieRanks.dualNumberTest ℂ) A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf (D.poincarePair t s)) =
    D.poincarePairClass (LieRanks.dualNumberTest ℂ ⊗ A.scheme)
      (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ t) (fst (LieRanks.dualNumberTest ℂ) A.scheme ≫ s) :=
    Quotient.sound ⟨D.poincarePairPullbackIso t s (fst (LieRanks.dualNumberTest ℂ) A.scheme)⟩
  exact h.symm.trans ((congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst (LieRanks.dualNumberTest ℂ) A.scheme).left) h₀).trans
    (map_one (HilbertConstruction.Line.Bundles.LineBundle.pullbackClassMonoidHom (fst (LieRanks.dualNumberTest ℂ) A.scheme).left)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareDualPairCoordinates
