import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Poisson Automorphy -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM

noncomputable section

/-! The complete PoissonAutomorphy specification, with every hypothesis and all five
conclusions, as an explicit named prerequisite. The separate audit checks
its type against the committed statement without using that theorem. -/

open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

universe u v w t

def PoissonAutomorphyInput : Prop := ∀
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {MpR : Type v} {MpF : Type w} {MpA : Type t}
    [Group MpR] [Group MpF] [Group MpA]
    (D : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ),
    let g := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ
    (∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      Summable (fun x : ι → ℚ => ‖f.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.diagonal x)‖)) ∧
    (∀ f : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.adelicSchwartz ι,
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional (D.rationalAction γ f) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaFunctional f) ∧
    (∀ (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      Summable (fun x : ι → ℚ => ‖RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.thetaTerm φ Z z x‖)) ∧
    (∀ Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι,
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet g Z ^ 2 = (g.complexify.denominator Z.matrix).det) ∧
    (∀ (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ),
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta (D.finiteAction γ φ) (g.transformSiegel Z) (g.jacobiChange Z z) =
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet g Z * (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor g Z z * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ Z z))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM
