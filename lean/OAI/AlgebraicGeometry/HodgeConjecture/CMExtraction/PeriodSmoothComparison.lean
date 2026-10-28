import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFamilies
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections
import OAI.AlgebraicGeometry.Comparison.Betti.KaehlerEquivalence

/-! # Period Smooth Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodSmoothComparison

noncomputable section

/-! Equality of the universal period covector and the actual smooth form in a chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates M]
  [IsManifold 𝓘(ℝ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) ∞ M] [IsManifold 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) ∞ M]
  (A : CommAlgCat.{0} ℂ) (φ : A →ₐ[ℂ] C(M, ℂ))
  (hφ : ∀ a, ContMDiff 𝓘(ℝ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℝ, ℂ) ∞ (φ a))
  (hφC : ∀ a, ContMDiff 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, ℂ) ∞ (φ a))
  (e : OpenPartialHomeomorph M RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (he : e ∈ atlas RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates M)
  (x : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) (hx : x ∈ e.target)

include hφC he hx in
omit [IsManifold 𝓘(ℝ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) ∞ M] in
theorem coordinateFunction_differentiable (a : A) :
    DifferentiableAt ℂ (fun y => φ a (e.symm y)) x := by
  have hs : ContMDiffAt 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) 𝓘(ℂ, RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) ∞ e.symm x :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hx
  exact ((hφC a).contMDiffAt.comp x hs).contDiffAt.differentiableAt (by simp)

def coordinateFunctionHom : A →ₐ[ℂ] RepresentationTheory.Theta.Geometric.DifferentialNaturality.functionsAt x where
  toFun a := ⟨fun y => φ a (e.symm y), coordinateFunction_differentiable A φ hφC e he x hx a⟩
  map_zero' := Subtype.ext (funext fun y => congrArg (fun f : C(M, ℂ) => f (e.symm y)) (map_zero φ))
  map_one' := Subtype.ext (funext fun y => congrArg (fun f : C(M, ℂ) => f (e.symm y)) (map_one φ))
  map_add' a b := Subtype.ext (funext fun y => congrArg (fun f : C(M, ℂ) => f (e.symm y)) (map_add φ a b))
  map_mul' a b := Subtype.ext (funext fun y => congrArg (fun f : C(M, ℂ) => f (e.symm y)) (map_mul φ a b))
  commutes' c := Subtype.ext (funext fun y => congrArg (fun f : C(M, ℂ) => f (e.symm y)) (φ.commutes c))

include hφC he hx in
theorem smoothKaehlerSymbol_inChart (a b : A) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (Comparison.Betti.Smooth.FormRealization.oneFormMap φ hφ (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm A
      (a • KaehlerDifferential.D ℂ A b))).val.inChart e x (fun _ => u) =
      φ a (e.symm x) * fderiv ℂ (fun y => φ b (e.symm y)) x u := by
  rw [Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm_smul_D, Comparison.Betti.KaehlerEquivalence.oneSymbol, Comparison.Betti.Smooth.FormRealization.oneFormMap_symbol]
  change ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction (φ a)
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap φ hφ b)).val).inChart e x) (fun _ => u) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
  change φ a (e.symm x) * (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Comparison.Betti.Smooth.FormRealization.zeroFormMap φ hφ b)).val.inChart e x
    (fun _ => u) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hx]
  change φ a (e.symm x) * (extDeriv ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (φ b)).inChart e) x) (fun _ => u) = _
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart, extDeriv_constOfIsEmpty,
    (coordinateFunction_differentiable A φ hφC e he x hx b).fderiv_restrictScalars ℝ]
  rfl

theorem smoothKaehler_inChart (form : KaehlerDifferential ℂ A) (u : RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates) :
    (Comparison.Betti.Smooth.FormRealization.oneFormMap φ hφ (Comparison.Betti.KaehlerEquivalence.kaehlerToOneForm A form)).val.inChart e x (fun _ => u) =
      RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x (AbelianScheme.TateComparison.FormConstants.differentialMap
        (CommAlgCat.ofHom (coordinateFunctionHom A φ hφC e he x hx)) form) u := by
  obtain ⟨r, rfl⟩ := KaehlerDifferential.linearCombination_surjective ℂ A form
  induction r using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero]
    rfl
  | add r t hr ht =>
    simp only [map_add, add_apply]
    have hadd (f g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm RepresentationTheory.Theta.Geometric.LinearTheta.BallCoordinates M 1) :
        (f + g).val.inChart e x (fun _ => u) =
          f.val.inChart e x (fun _ => u) + g.val.inChart e x (fun _ => u) :=
      congrArg (fun q => q x (fun _ => u)) (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add f.val g.val e)
    exact (hadd _ _).trans (congrArg₂ (· + ·) hr ht)
  | single b a =>
    simp only [Finsupp.linearCombination_single]
    rw [smoothKaehlerSymbol_inChart A φ hφ hφC e he x hx]
    let f : A ⟶ RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodTest x := CommAlgCat.ofHom (coordinateFunctionHom A φ hφC e he x hx)
    have hs := RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_smul f a (KaehlerDifferential.D ℂ A b)
    have hd := RepresentationTheory.Theta.Geometric.DifferentialNaturality.differentialMap_D f b
    have h₁ := congrArg (fun w => RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x w u) hs
    have h₂ := congrArg (fun w => RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential x w u) hd
    have h := RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential_smul x (f.hom a) (AbelianScheme.TateComparison.FormConstants.differentialMap f (KaehlerDifferential.D ℂ A b))
    have h' := congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => L u) h
    exact (h₁.trans (h'.trans (congrArg ((φ a (e.symm x)) * ·)
      (h₂.trans (congrArg (fun L : RepresentationTheory.Theta.Geometric.LinearTheta.Cotangent => L u) (RepresentationTheory.Theta.Geometric.DifferentialNaturality.periodDifferential_D x (f.hom b))))))).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodSmoothComparison
