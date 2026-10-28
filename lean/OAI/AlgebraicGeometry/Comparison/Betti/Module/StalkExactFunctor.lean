import OAI.Analysis.DifferentialForms.Manifold.ComplexSheafCategory
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Stalk Exact Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor.Holomorphic

noncomputable section

/-! Exactness of actual module stalks, as filtered colimits of sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X : TopCat.{0}} (x : X)

instance moduleStalk_preservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x) := by
  have hcolim : PreservesFiniteLimits (colim (J := (TopologicalSpace.OpenNhds x)ᵒᵖ)
      (C := ModuleCat.{0} ℂ)) := inferInstance
  have hwhisker : PreservesFiniteLimits
      ((Functor.whiskeringLeft (TopologicalSpace.OpenNhds x)ᵒᵖ
        (TopologicalSpace.Opens X)ᵒᵖ (ModuleCat.{0} ℂ)).obj
          (TopologicalSpace.OpenNhds.inclusion x).op) := inferInstance
  dsimp only [TopCat.Presheaf.stalkFunctor]
  infer_instance

instance moduleStalk_preservesHomology :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℂ) x).PreservesHomology := by
  infer_instance

end

end OAI.AlgebraicGeometry.Comparison.Betti.Module.StalkExactFunctor.Holomorphic
