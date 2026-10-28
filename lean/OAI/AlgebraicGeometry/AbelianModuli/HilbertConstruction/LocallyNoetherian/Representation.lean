import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.Functor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterFiniteness
import Mathlib.CategoryTheory.Yoneda

/-! # Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.Representation

noncomputable section

/-! An actual representing scheme for the Hilbert-family presheaf on locally noetherian tests, under the constructed degree bounds and finite numerical Hilbert test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def generatedLocallyNoetherianParameter (S : Scheme.{u}) [IsLocallyNoetherian S]
    (n B : ℕ) (r : ℕ → ℕ) (N : ℕ) : Relative.Functor.LocallyNoetherianTest S where
  obj := Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N
  property := by
    have : LocallyOfFinitePresentation (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom :=
      Generated.ParameterFiniteness.truncatedGeneratedParameters_locallyFinitePresentation S n B r N
    exact LocallyOfFiniteType.isLocallyNoetherian (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).hom

def locallyNoetherianHomEquiv {S : Scheme.{u}} (T U : Relative.Functor.LocallyNoetherianTest S) :
    (T.obj ⟶ U.obj) ≃ (T ⟶ U) := InducedCategory.homEquiv.symm

variable (S : Scheme.{u}) [IsLocallyNoetherian S] {n B N : ℕ} {P : Polynomial ℚ}
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

def locallyNoetherianHilbertClassifyingIso : Relative.Functor.locallyNoetherianHilbertFunctor S n P ≅
    yoneda.obj (generatedLocallyNoetherianParameter S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N) :=
  NatIso.ofComponents (fun T =>
    ((Relative.ParameterEquivalence.relativeProjectiveHilbertParameterEquiv (T := T.unop.obj) hN hflat htest hr).trans
      (locallyNoetherianHomEquiv T.unop
        (generatedLocallyNoetherianParameter S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N))).toIso) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro F
    apply ObjectProperty.hom_ext
    exact RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_natural
      (V := T.unop.obj) (W := U.unop.obj) F hN hflat htest hr f.unop.hom)

include hN hflat htest hr in
theorem locallyNoetherianHilbert_isRepresentable : (Relative.Functor.locallyNoetherianHilbertFunctor S n P).IsRepresentable :=
  Functor.IsRepresentable.mk' (locallyNoetherianHilbertClassifyingIso S hN hflat htest hr).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.Representation
