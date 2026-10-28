import Mathlib.Algebra.Homology.HomologySequence

/-! # Vanishing Homology Exact Sequences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VanishingHomologyExactSequences

noncomputable section

/-! Adjacent vanishing in a short exact sequence of complexes forces vanishing of the remaining cohomology group. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w

theorem shortExact_homology_X3_isZero {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (h₂ : IsZero (S.X₂.homology i)) (h₁ : IsZero (S.X₁.homology j)) :
    IsZero (S.X₃.homology i) :=
  (hS.homology_exact₃ i j hij).isZero_of_both_isZero h₂ h₁

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VanishingHomologyExactSequences
