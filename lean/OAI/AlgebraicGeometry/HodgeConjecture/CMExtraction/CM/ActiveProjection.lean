import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActivePlace
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary

/-! # Active Projection -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveProjection.Approximation

noncomputable section

/-! The active SL3 projection on the actual finite local unitary factor.
On the original rational CM group it is exactly entrywise application of
the specified q-adic embedding. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Special
open OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous OAI.RepresentationTheory.Theta.Adelic.RationalSU

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneUnitary.Quadratic

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)))ˣ)

def cmActiveSL :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E) H.val (.inr (ActivePlace.Approximation.cmActivePlace E σ))) →ₜ*
      Matrix.SpecialLinearGroup (Fin 3) (Padic q) where
  toMonoidHom := (Matrix.SpecialLinearGroup.map (ActivePlace.Approximation.cmActiveCompletion E σ).toRingHom).comp
    (RepresentationTheory.Theta.Adelic.SplitUnitary.Special.plusSpecialUnitary (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
      (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0)
      (RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.localizedUnit (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) H (.inr (ActivePlace.Approximation.cmActivePlace E σ))))
  continuous_toFun := (ActivePlace.Approximation.cmActiveCompletion_continuous E σ).specialLinearGroup_map.comp
    (RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous.plusSpecialUnitary_continuous (ActivePlace.Approximation.cmActiveRoot E σ δ) (ActivePlace.Approximation.cmActiveRoot_sq E σ δ hδ)
      (ActivePlace.Approximation.cmActiveRoot_ne_zero E σ δ hδ0) _)

theorem cmActiveSL_matrix
    (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E) H.val (.inr (ActivePlace.Approximation.cmActivePlace E σ)))) :
    (cmActiveSL E σ δ hδ hδ0 H g).val =
      g.val.val.map (ActivePlace.Approximation.cmActiveQuadraticProjection E σ δ hδ hδ0) := rfl

theorem cmActiveSL_rational_matrix (g : RepresentationTheory.Theta.Adelic.SpecialUnitary.SU H.val) :
    (cmActiveSL E σ δ hδ hδ0 H
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield E) H (.inr (ActivePlace.Approximation.cmActivePlace E σ)) g)).val =
      g.val.val.map (σ.comp (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).toRingHom) := by
  apply Matrix.ext
  intro i j
  exact ActivePlace.Approximation.cmActiveQuadraticProjection_rational E σ δ hδ hδ0 (g.val.val i j)

variable (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)

theorem cmActiveSL_original (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b) :
    cmActiveSL E σ δ hδ hδ0 (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield E) (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0)
        (.inr (ActivePlace.Approximation.cmActivePlace E σ)) (Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E δ hδ hδ0 b hb hb0 g)) =
      Matrix.SpecialLinearGroup.map σ g.val := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact ActivePlace.Approximation.cmActiveQuadraticProjection_cm_rational E σ δ hδ hδ0 (g.val.val i j)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActiveProjection.Approximation
