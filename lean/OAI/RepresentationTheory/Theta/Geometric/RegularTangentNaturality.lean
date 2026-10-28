import OAI.RepresentationTheory.Theta.Geometric.RegularTangent
import OAI.RepresentationTheory.Theta.Geometric.Affine.TangentNaturality
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

/-! # Regular Tangent Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.RegularTangentNaturality

noncomputable section

/-! Differentiating a genuine affine scheme map in regular charts agrees
with precomposing the corresponding algebraic point derivation. -/

open scoped ContDiff _root_.Topology
open _root_.CategoryTheory OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  {n m : ℕ} (h : A →ₐ[ℂ] B)
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
  (f : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
  (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)

include he hf hx hfx

theorem regularChart_derivative_naturality (a : A) (v : Fin n → ℂ) :
    fderiv ℂ (fun z => e.symm z (h a)) (e x) v =
      fderiv ℂ (fun z => f.symm z a) (f (x.comp h))
        (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) v) := by
  let F := fun z => f ((e.symm z).comp h)
  have hF : DifferentiableAt ℂ F (e x) :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx).differentiableAt (by simp)
  have hFa : DifferentiableAt ℂ (fun z => f.symm z a) (F (e x)) := by
    change DifferentiableAt ℂ (fun z => f.symm z a) (f ((e.symm (e x)).comp h))
    rw [e.left_inv hx]
    exact (hf.1 a).differentiableOn (by simp) |>.differentiableAt
      (f.open_target.mem_nhds (f.map_source hfx))
  have heq : (fun z => e.symm z (h a)) =ᶠ[nhds (e x)]
      ((fun z => f.symm z a) ∘ F) := by
    filter_upwards [AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood h e f x hx hfx] with z hz
    change ((e.symm z).comp h) a = f.symm (f ((e.symm z).comp h)) a
    exact (congrArg (fun p : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A => p a) (f.left_inv hz.2)).symm
  have hder := heq.fderiv_eq.trans (fderiv_comp (e x) hFa hF)
  have hp : F (e x) = f (x.comp h) := congrArg (fun p : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B => f (p.comp h))
    (e.left_inv hx)
  rw [hp] at hder
  exact congrArg (fun d : (Fin n → ℂ) →L[ℂ] ℂ => d v) hder

variable [Algebra A B] [IsScalarTower ℂ A B]
  [Algebra A ℂ] [Algebra B ℂ] [IsScalarTower ℂ A ℂ] [IsScalarTower ℂ B ℂ]
  [IsScalarTower A B ℂ]

omit h hfx in
theorem regularChart_derivation_naturality
    (hfx : x.comp (IsScalarTower.toAlgHom ℂ A B) ∈ f.source)
    (hxscalar : ∀ b : B, algebraMap B ℂ b = x b)
    (hyscalar : ∀ a : A, algebraMap A ℂ a = (x.comp (IsScalarTower.toAlgHom ℂ A B)) a)
    (v : Fin n → ℂ) :
    RegularTangent.regularChartDerivation f hf (x.comp (IsScalarTower.toAlgHom ℂ A B)) hfx hyscalar
        (fderiv ℂ (fun z => f ((e.symm z).comp (IsScalarTower.toAlgHom ℂ A B))) (e x) v) =
      (RegularTangent.regularChartDerivation e he x hx hxscalar v).compAlgebraMap A := by
  apply Derivation.ext
  intro a
  exact (regularChart_derivative_naturality (IsScalarTower.toAlgHom ℂ A B)
    e f he hf x hx hfx a v).symm

omit h hfx in
theorem regularChart_affineTangent_naturality
    (hfx : x.comp (IsScalarTower.toAlgHom ℂ A B) ∈ f.source)
    (hxscalar : ∀ b : B, algebraMap B ℂ b = x b)
    (hyscalar : ∀ a : A, algebraMap A ℂ a = (x.comp (IsScalarTower.toAlgHom ℂ A B)) a)
    (v : Fin n → ℂ) :
    (Affine.Tangents.derivationAffineTangentEquiv ℂ A
      (RegularTangent.regularChartDerivation f hf (x.comp (IsScalarTower.toAlgHom ℂ A B)) hfx hyscalar
        (fderiv ℂ (fun z => f ((e.symm z).comp (IsScalarTower.toAlgHom ℂ A B))) (e x) v))).val =
      (Affine.Tangents.derivationAffineTangentEquiv ℂ B (RegularTangent.regularChartDerivation e he x hx hxscalar v)).val ≫
        AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ A B (IsScalarTower.toAlgHom ℂ A B) := by
  exact (congrArg (fun δ : Derivation ℂ A ℂ => (Affine.Tangents.derivationAffineTangentEquiv ℂ A δ).val)
    (regularChart_derivation_naturality e f he hf x hx hfx hxscalar hyscalar v)).trans
      (Affine.TangentNaturality.derivationAffineTangent_compAlgebraMap _)

end

end OAI.RepresentationTheory.Theta.Geometric.RegularTangentNaturality
