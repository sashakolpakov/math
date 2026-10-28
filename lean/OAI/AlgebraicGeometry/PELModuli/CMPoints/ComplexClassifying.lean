import OAI.AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFiber

/-! # Complex Classifying -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexClassifying

noncomputable section

/-! Actual complex points of the original fine PEL model give
injective classifying maps over the fixed coefficient embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (κ : K →+* ℂ)

def finePELClassifyingPoint (x : M.ComplexPoints κ) :
    Over.mk (Spec.map (CommRingCat.ofHom κ)) ⟶ M.space :=
  Over.homMk (IntrinsicFiber.finePELComplexPoint M κ x) (IntrinsicFiber.finePELComplexPoint_base M κ x)

omit [NumberField K] in
theorem finePELClassifyingPoint_injective : Function.Injective (finePELClassifyingPoint M κ) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply CategoryTheory.Limits.pullback.hom_ext
  · exact congrArg Over.Hom.left h
  · exact x.w.trans y.w.symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ComplexClassifying
