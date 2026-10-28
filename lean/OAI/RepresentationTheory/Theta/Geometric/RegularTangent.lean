import OAI.RepresentationTheory.Theta.Geometric.TangentRealization
import OAI.RepresentationTheory.Theta.Geometric.Affine.Tangents
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! # Regular Tangent -/

namespace OAI.RepresentationTheory.Theta.Geometric.RegularTangent

noncomputable section

/-! Regular functions detect every analytic tangent vector in a native
affine chart. Together with the actual point-derivation realization this
identifies analytic and algebraic tangent coordinates. -/

open scoped ContDiff _root_.Topology

variable {S : Type} [CommRing S] [Algebra ℂ S] {n : ℕ}
  (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (Fin n → ℂ))
  (he : e ∈ AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas S n) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (hx : x ∈ e.source)

include he hx

theorem regularChart_tangent_zero (v : Fin n → ℂ)
    (hv : ∀ a : S, fderiv ℂ (fun z => e.symm z a) (e x) v = 0) : v = 0 := by
  obtain ⟨g, hg, hcoords⟩ := he.2
  have hd (a : S) : DifferentiableAt ℂ (fun z => e.symm z a) (e x) :=
    (he.1 a).differentiableOn (by simp) |>.differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))
  funext i
  obtain ⟨a, k, hcoord⟩ := hcoords i
  have heq : (fun z : Fin n → ℂ => z i * (e.symm z g) ^ k) =ᶠ[nhds (e x)]
      (fun z => e.symm z a) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with z hz
    have hzi : z i = e.symm z a / (e.symm z g) ^ k :=
      (congrArg (fun w => w i) (e.right_inv hz)).symm.trans
        (hcoord (e.symm z) (e.map_target hz))
    rw [hzi, div_mul_cancel₀ _ (pow_ne_zero k (hg _ (e.map_target hz)))]
  have hden : (e.symm (e x) g) ^ k ≠ 0 := by rw [e.left_inv hx]; exact pow_ne_zero k (hg x hx)
  have hder := (hasFDerivAt_apply i (e x)).mul ((hd g).hasFDerivAt.pow k)
  have hvalue := congrArg (fun f : (Fin n → ℂ) →L[ℂ] ℂ => f v)
    (hder.fderiv.symm.trans heq.fderiv_eq)
  have hzero : (e.symm (e x) g) ^ k * v i = 0 := by
    simpa [hv] using hvalue
  exact (mul_eq_zero.mp hzero).resolve_left hden

theorem regularChart_tangent_ext (v w : Fin n → ℂ)
    (hv : ∀ a : S, fderiv ℂ (fun z => e.symm z a) (e x) v =
      fderiv ℂ (fun z => e.symm z a) (e x) w) : v = w := by
  apply sub_eq_zero.mp
  apply regularChart_tangent_zero e he x hx
  intro a
  rw [map_sub, hv a, sub_self]

variable [Algebra S ℂ] [IsScalarTower ℂ S ℂ]
  (hscalar : ∀ a : S, algebraMap S ℂ a = x a)

def regularChartDerivation : (Fin n → ℂ) →ₗ[ℂ] Derivation ℂ S ℂ where
  toFun := AlgebraicGeometry.HodgeConjecture.DegreeTwo.AnalyticDerivation.Constructions.analyticChartDerivation x hscalar e hx
    (fun a => (he.1 a).differentiableOn (by simp) |>.differentiableAt
      (e.open_target.mem_nhds (e.map_source hx)))
  map_add' v w := by
    apply Derivation.ext
    intro a
    exact map_add (fderiv ℂ (fun z => e.symm z a) (e x)) v w
  map_smul' c v := by
    apply Derivation.ext
    intro a
    exact map_smul (fderiv ℂ (fun z => e.symm z a) (e x)) c v

theorem regularChartDerivation_injective :
    Function.Injective (regularChartDerivation e he x hx hscalar) := by
  intro v w h
  apply regularChart_tangent_ext e he x hx
  intro a
  exact congrArg (fun δ : Derivation ℂ S ℂ => δ a) h

theorem regularChartDerivation_surjective [Algebra.Smooth ℂ S] :
    Function.Surjective (regularChartDerivation e he x hx hscalar) := by
  have hA : (inferInstance : Algebra S ℂ) = x.toRingHom.toAlgebra :=
    Algebra.algebra_ext _ _ hscalar
  cases hA
  let : Algebra S ℂ := x.toRingHom.toAlgebra
  intro δ
  obtain ⟨v, hv⟩ := TangentRealization.exists_tangent_in_regular_chart e he x hx δ
  exact ⟨v, Derivation.ext hv⟩

def regularChartDerivationEquiv [Algebra.Smooth ℂ S] :
    (Fin n → ℂ) ≃ₗ[ℂ] Derivation ℂ S ℂ :=
  LinearEquiv.ofBijective (regularChartDerivation e he x hx hscalar)
    ⟨regularChartDerivation_injective e he x hx hscalar,
      regularChartDerivation_surjective e he x hx hscalar⟩

def regularChartAffineTangentEquiv [Algebra.Smooth ℂ S] :
    (Fin n → ℂ) ≃ Affine.Tangents.affineTangentPoints ℂ S :=
  (regularChartDerivationEquiv e he x hx hscalar).toEquiv.trans (Affine.Tangents.derivationAffineTangentEquiv ℂ S)

end

end OAI.RepresentationTheory.Theta.Geometric.RegularTangent
