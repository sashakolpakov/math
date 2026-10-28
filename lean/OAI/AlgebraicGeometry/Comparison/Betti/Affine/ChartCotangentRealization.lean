import OAI.AlgebraicGeometry.Comparison.Betti.Affine.PointDifferentialRank
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.RegularDifferentialsSpan

/-! # Chart Cotangent Realization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartCotangentRealization

noncomputable section

section

/-! Pointwise realization of actual Kähler differentials in a native regular chart. -/

open scoped ContDiff TensorProduct

variable {A : Type} [CommRing A] [Algebra ℂ A] {n : ℕ}

def affineChartRegularDifferential
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (a : A) : Module.Dual ℂ (Fin n → ℂ) :=
  (fderiv ℂ (fun z => e.symm z a) (e x)).toLinearMap

def affineChartRegularDerivation
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    let _ : Module A (Module.Dual ℂ (Fin n → ℂ)) :=
      Module.compHom (Module.Dual ℂ (Fin n → ℂ)) x.toRingHom
    Derivation ℂ A (Module.Dual ℂ (Fin n → ℂ)) := by
  let : Module A (Module.Dual ℂ (Fin n → ℂ)) :=
    Module.compHom (Module.Dual ℂ (Fin n → ℂ)) x.toRingHom
  have hd (a : A) : DifferentiableAt ℂ (fun z => e.symm z a) (e x) :=
    ((he.1 a).contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
      (by simp)
  exact
    { toFun := affineChartRegularDifferential e x
      map_add' := fun a b => by
        ext v
        simp only [affineChartRegularDifferential, map_add]
        rw [fderiv_fun_add (hd a) (hd b)]
        rfl
      map_smul' := fun c a => by
        ext v
        simp only [affineChartRegularDifferential, map_smul, smul_eq_mul]
        rw [fderiv_fun_mul (differentiableAt_const c) (hd a)]
        simp
      map_one_eq_zero' := by
        ext v
        simp [affineChartRegularDifferential]
      leibniz' := fun a b => by
        apply LinearMap.ext
        intro v
        change fderiv ℂ (fun z => e.symm z (a * b)) (e x) v =
          x a * fderiv ℂ (fun z => e.symm z b) (e x) v +
            x b * fderiv ℂ (fun z => e.symm z a) (e x) v
        simp only [map_mul]
        rw [fderiv_fun_mul (hd a) (hd b)]
        change e.symm (e x) a * _ + e.symm (e x) b * _ = x a * _ + x b * _
        rw [e.left_inv hx]
        rfl }

def affineChartCotangentRealization
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    PointDifferentialRank.affinePointDifferentialFiber x →ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  let : Module A (Module.Dual ℂ (Fin n → ℂ)) :=
    Module.compHom (Module.Dual ℂ (Fin n → ℂ)) x.toRingHom
  let : IsScalarTower ℂ A (Module.Dual ℂ (Fin n → ℂ)) :=
    ⟨fun c a v => by
      change x (c • a) • v = c • (x a • v)
      rw [map_smul, smul_assoc]⟩
  let : IsScalarTower A ℂ (Module.Dual ℂ (Fin n → ℂ)) :=
    ⟨fun a c v => by
      change (x a * c) • v = x a • (c • v)
      exact mul_smul _ _ _⟩
  exact (affineChartRegularDerivation e he x hx).liftKaehlerDifferential.liftBaseChange ℂ

theorem affineChartCotangentRealization_D
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source)
    (a : A) :
    let _ : Algebra A ℂ := x.toRingHom.toAlgebra
    affineChartCotangentRealization e he x hx (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a) =
      affineChartRegularDifferential e x a := by
  let : Module A (Module.Dual ℂ (Fin n → ℂ)) :=
    Module.compHom (Module.Dual ℂ (Fin n → ℂ)) x.toRingHom
  let : IsScalarTower ℂ A (Module.Dual ℂ (Fin n → ℂ)) :=
    ⟨fun c a v => by
      change x (c • a) • v = c • (x a • v)
      rw [map_smul, smul_assoc]⟩
  dsimp [affineChartCotangentRealization]
  rw [one_smul, Derivation.liftKaehlerDifferential_comp_D]
  rfl

theorem affineChartCotangentRealization_surjective
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A n) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    Function.Surjective (affineChartCotangentRealization e he x hx) := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← RegularDifferentialsSpan.affineRegularChart_differentials_span e he x hx]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact ⟨1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a,
    affineChartCotangentRealization_D e he x hx a⟩

theorem affineChartCotangentRealization_bijective [IsDomain A] [Algebra.Smooth ℂ A]
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A))
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (hx : x ∈ e.source) :
    Function.Bijective (affineChartCotangentRealization e he x hx) := by
  let : Algebra A ℂ := x.toRingHom.toAlgebra
  have hdim : Module.finrank ℂ (PointDifferentialRank.affinePointDifferentialFiber x) =
      Module.finrank ℂ (Module.Dual ℂ (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ)) := by
    simpa using PointDifferentialRank.affinePointDifferentialFiber_finrank x
  have hs := affineChartCotangentRealization_surjective e he x hx
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hs, hs⟩

end

/-! The actual chart differential of an affine morphism acts on regular-function covectors by pullback. -/

open scoped ContDiff _root_.Topology

open Filter

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  {n m : ℕ}

theorem affineChartRegularDifferential_comap
    (h : A →ₐ[ℂ] B)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source)
    (a : A) (v : Fin n → ℂ) :
    affineChartRegularDifferential e x (h a) v =
      affineChartRegularDifferential f (x.comp h) a
        (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x) v) := by
  have heq : (fun z => e.symm z (h a)) =ᶠ[𝓝 (e x)]
      (fun z => f.symm (f ((e.symm z).comp h)) a) := by
    filter_upwards [ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood h e f x hx hfx] with z hz
    rw [f.left_inv hz.2]
    rfl
  have hF := (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx).differentiableAt (by simp)
  have hfa : DifferentiableAt ℂ (fun w => f.symm w a)
      (f ((e.symm (e x)).comp h)) := by
    rw [e.left_inv hx]
    exact ((hf.1 a).contDiffAt
      (f.open_target.mem_nhds (f.map_source hfx))).differentiableAt (by simp)
  have hchain := fderiv_comp (e x) hfa hF
  simp only [Function.comp_def] at hchain
  change fderiv ℂ (fun z => e.symm z (h a)) (e x) v = _
  rw [heq.fderiv_eq, hchain, ContinuousLinearMap.comp_apply, e.left_inv hx]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartCotangentRealization
