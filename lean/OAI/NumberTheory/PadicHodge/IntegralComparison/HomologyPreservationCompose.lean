import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Homology Preservation Compose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose

noncomputable section

/-! Preserving the homology of a fixed complex survives an exact change of coefficients. -/

open _root_.CategoryTheory Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
  (F : C ⥤ D) (G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] (S : ShortComplex C)

theorem left [F.PreservesLeftHomologyOf S] : (F ⋙ G).PreservesLeftHomologyOf S where
  isPreservedBy h := by
    have := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
    have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
    exact { g := inferInstance, f' := inferInstance }

theorem right [F.PreservesRightHomologyOf S] : (F ⋙ G).PreservesRightHomologyOf S where
  isPreservedBy h := by
    have := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
    have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
    exact { f := inferInstance, g' := inferInstance }

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyPreservationCompose
