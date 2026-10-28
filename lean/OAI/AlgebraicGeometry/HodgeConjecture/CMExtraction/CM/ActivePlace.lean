import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel
import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPadic
import OAI.RepresentationTheory.Theta.Adelic.SplitUnitary
import OAI.RepresentationTheory.Weil.AdelicSplitting.Integral

/-! # Active Place -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActivePlace.Approximation

noncomputable section

/-! The finite place and split quadratic projection determined by the
specified CM-field embedding into Q_q. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticModel.CM OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra OAI.RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous

instance finiteCompletionCharZero (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.completionCharZero F (.inr v)

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  {q : ℕ} [Fact q.Prime] (σ : E →+* Padic q)

def cmActivePlace : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)) :=
  PELModuli.CMPoints.LocalPadic.embeddingPlace (σ.comp (algebraMap (maximalRealSubfield E) E))

def cmActiveCompletion : (cmActivePlace E σ).adicCompletion (maximalRealSubfield E) ≃+* Padic q :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv (σ.comp (algebraMap (maximalRealSubfield E) E))

omit [IsCMField E] in
theorem cmActiveCompletion_continuous : Continuous (cmActiveCompletion E σ) :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionEquiv_continuous _

omit [IsCMField E] in
theorem cmActiveCompletion_rational (x : maximalRealSubfield E) :
    cmActiveCompletion E σ (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield E) (.inr (cmActivePlace E σ)) x) =
      σ (x : E) :=
  PELModuli.CMPoints.LocalPadic.embeddingCompletionHom_coe (σ.comp (algebraMap (maximalRealSubfield E) E)) x

def cmActiveRoot (δ : E) : (cmActivePlace E σ).adicCompletion (maximalRealSubfield E) :=
  (cmActiveCompletion E σ).symm (σ δ)

theorem cmActiveRoot_sq (δ : E) (hδ : IsCMField.complexConj E δ = -δ) :
    cmActiveRoot E σ δ ^ 2 =
      RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield E) (.inr (cmActivePlace E σ)) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) := by
  apply (cmActiveCompletion E σ).injective
  rw [map_pow, cmActiveRoot, RingEquiv.apply_symm_apply, cmActiveCompletion_rational]
  exact (map_pow σ δ 2).symm

omit [IsCMField E] in
theorem cmActiveRoot_ne_zero (δ : E) (hδ0 : δ ≠ 0) : cmActiveRoot E σ δ ≠ 0 :=
  (map_ne_zero (cmActiveCompletion E σ).symm).mpr ((map_ne_zero σ).mpr hδ0)

def cmActiveQuadraticProjection (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
      (.inr (cmActivePlace E σ)) →+* Padic q :=
  (cmActiveCompletion E σ).toRingHom.comp
    (RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra.plus (cmActiveRoot E σ δ) (cmActiveRoot_sq E σ δ hδ) (cmActiveRoot_ne_zero E σ δ hδ0))

theorem cmActiveQuadraticProjection_continuous
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) :
    Continuous (cmActiveQuadraticProjection E σ δ hδ hδ0) :=
  (cmActiveCompletion_continuous E σ).comp
    (RepresentationTheory.Theta.Adelic.SplitUnitary.Continuous.plus_continuous (cmActiveRoot E σ δ) (cmActiveRoot_sq E σ δ hδ)
      (cmActiveRoot_ne_zero E σ δ hδ0))

theorem cmActiveQuadraticProjection_rational
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (z : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)) :
    cmActiveQuadraticProjection E σ δ hδ hδ0
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
        (.inr (cmActivePlace E σ)) z) = σ (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0 z) := by
  change cmActiveCompletion E σ
    (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield E) (.inr (cmActivePlace E σ)) z.re +
      cmActiveRoot E σ δ * RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield E) (.inr (cmActivePlace E σ)) z.im) =
    σ (ThetaCycle.QuadraticModel.CM.cmQuadraticMap E δ hδ z)
  rw [map_add, map_mul, cmActiveRoot, RingEquiv.apply_symm_apply,
    cmActiveCompletion_rational, cmActiveCompletion_rational, ThetaCycle.QuadraticModel.CM.cm_quadratic_map_apply,
    map_add, map_mul]
  congr 1
  exact mul_comm _ _

theorem cmActiveQuadraticProjection_cm_rational
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (x : E) :
    cmActiveQuadraticProjection E σ δ hδ hδ0
      (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ)
        (.inr (cmActivePlace E σ)) ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm x)) = σ x := by
  rw [cmActiveQuadraticProjection_rational, AlgEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CM.ActivePlace.Approximation
