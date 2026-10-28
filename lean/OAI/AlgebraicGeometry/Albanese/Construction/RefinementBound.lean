import OAI.AlgebraicGeometry.Albanese.Construction.FiniteRefinements

/-! # Refinement Bound -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.RefinementBound

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

/-- Each fiber of a word morphism is a Noetherian scheme. -/
theorem wordFiber_noetherian (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (n : ℕ) (y : A.toOver.left) :
    IsNoetherian ((ImageWords.wordMap X A a n).left.fiber y) := by
  have : LocallyOfFiniteType ((ImageWords.wordMap X A a n).left.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (Limits.pullback.snd (ImageWords.wordMap X A a n).left
      (A.toOver.left.fromSpecResidueField y))
    infer_instance
  have : IsLocallyNoetherian ((ImageWords.wordMap X A a n).left.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((ImageWords.wordMap X A a n).left.fiberToSpecResidueField y)
  exact {}

/-- The number of irreducible components of a fixed word fiber. This natural
number bounds all equal-dimensional generated refinements of this target. -/
def wordFiberComponentCount (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (b : X.toOver ⟶ B.toOver) (y : B.toOver.left) : ℕ :=
  Nat.card (irreducibleComponents
    ((ImageWords.wordMap X B b (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap)).left.fiber y))

/-- The sizes of the finite fibers of all equal-dimensional generated
refinements are bounded by one fixed source fiber, independently of the
refining abelian variety. -/
theorem refinement_fiber_card_bound (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    [ConnectedSpace X.carrier] (x₀ : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (φ : A.toOver ⟶ B.toOver) [IsMonHom φ] (hφ : a ≫ φ = b)
    (ha : GeneratedClosed.Generates X A a) (hb : GeneratedClosed.Generates X B b)
    (hd : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension A.variety.structureMap =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap) (y : B.toOver.left) :
    Nat.card (φ.left.fiber y) ≤ wordFiberComponentCount X B b y := by
  let m := Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension B.variety.structureMap
  have : Surjective (ImageWords.wordMap X A a m).left :=
    GeneratingWords.generating_word_surjective X x₀ A a ha m hd.le
  have : IsFinite φ.left := FiniteRefinements.refinement_finite X A B a b φ hφ hb hd
  have hword : (ImageWords.wordMap X A a m).left ≫ φ.left = (ImageWords.wordMap X B b m).left := by
    have h := GeneratingWords.wordMap_comp X A B a φ m
    rw [hφ] at h
    exact congrArg Over.Hom.left h
  have : IsNoetherian ((ImageWords.wordMap X B b m).left.fiber y) := wordFiber_noetherian X B b m y
  have : Finite (irreducibleComponents (((ImageWords.wordMap X A a m).left ≫ φ.left).fiber y)) := by
    rw [hword]
    exact NoetherianSpace.finite_irreducibleComponents
  have hbound := FiniteRefinements.fiber_card_le_components_of_factor (ImageWords.wordMap X A a m).left φ.left y
  rw! [hword] at hbound
  exact hbound

end

end OAI.AlgebraicGeometry.Albanese.Construction.RefinementBound
