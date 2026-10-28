import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveProjection
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SplitInverseContinuous

/-! # Active Inverse -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveInverse.Approximation

noncomputable section

/-! The active SL projection has a continuous inverse in its actual local topology. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)))ˣ)
  (hH : (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) H
    (.inr (ActivePlace.Approximation.cmActivePlace E σ))).val.conjTranspose =
      (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) H
        (.inr (ActivePlace.Approximation.cmActivePlace E σ))).val)

def cmActiveSLInverse : Matrix.SpecialLinearGroup (Fin 3) (Padic q) →ₜ*
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E) H.val (.inr (ActivePlace.Approximation.cmActivePlace E σ))) where
  toMonoidHom := ((RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
    (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0)
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) H
      (.inr (ActivePlace.Approximation.cmActivePlace E σ))) hH).symm.toMonoidHom).comp
        (Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).symm.toRingHom)
  continuous_toFun := (SplitInverseContinuous.Approximation.specialUnitaryEquivSL_symm_continuous (ActivePlace.Approximation.cmActiveRoot E σ δ)
    (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ) (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0) _ hH).comp
      (PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_symm_continuous
        (σ.comp (algebraMap (maximalRealSubfield E) E))).specialLinearGroup_map

theorem cmActiveSLInverse_left (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E) H.val (.inr (ActivePlace.Approximation.cmActivePlace E σ)))) :
    cmActiveSLInverse E σ δ hδ hδ0 H hH (ActiveProjection.Approximation.cmActiveSL E σ δ hδ hδ0 H g) = g := by
  let e := RepresentationTheory.Theta.Adelic.SplitUnitary.Special.specialUnitaryEquivSL (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
    (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0)
    (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) H
      (.inr (ActivePlace.Approximation.cmActivePlace E σ))) hH
  change e.symm (Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).symm.toRingHom
    (Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).toRingHom (e g))) = g
  have hm : Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).symm.toRingHom
      (Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).toRingHom (e g)) = e g := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    exact (ActivePlace.Approximation.cmActiveCompletion E σ).symm_apply_apply ((e g).val i j)
  exact (congrArg e.symm hm).trans (e.symm_apply_apply g)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveInverse.Approximation
