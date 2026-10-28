import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Etale.Kaehler

/-! # Etale Differential -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleDifferential.Constructions.Construction

noncomputable section

open scoped ContDiff _root_.Manifold _root_.Topology
open Filter OAI.AlgebraicGeometry.ComplexPoints.Analytic.SmoothClosedImmersion

/-- Etale pullback preserves the dimension of the native affine models,
as seen by base change of the actual Kahler differential modules. -/
theorem genericDifferentialRank_eq_of_formallyEtale
    {A B : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
    [CommRing B] [Algebra ℂ B] [IsDomain B]
    (h : A →ₐ[ℂ] B) (hh : h.toRingHom.FormallyEtale) :
    Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B = Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A := by
  let := h.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq' h.comp_algebraMap.symm
  let : Algebra.FormallyEtale A B := hh
  let p : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  exact (Module.rankAtStalk_isBaseChange
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ A B) p).trans
      (Foundations.Scheme.SmoothDomainDimension.Algebraic.kaehler_rankAtStalk_eq_generic _)

/-- Formal unramifiedness kills any point derivation that vanishes on
the base algebra. -/
theorem point_derivation_eq_zero_of_unramified
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (h : A →ₐ[ℂ] B) (hh : h.toRingHom.FormallyUnramified)
    (x : B →ₐ[ℂ] ℂ) (D : B → ℂ)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = x a * D b + x b * D a)
    (hbase : ∀ a, D (h a) = 0) :
    ∀ b, D b = 0 := by
  let := h.toRingHom.toAlgebra
  let := x.toRingHom.toAlgebra
  let := (x.comp h).toRingHom.toAlgebra
  let : IsScalarTower A B ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FormallyUnramified A B := hh
  let d : Derivation A B ℂ :=
    { toFun := D
      map_add' := hadd
      map_smul' := fun a b => by
        change D (h a * b) = x (h a) * D b
        rw [hmul, hbase, mul_zero, add_zero]
      map_one_eq_zero' := by
        change D 1 = 0
        simpa only [map_one] using hbase 1
      leibniz' := hmul }
  let : Subsingleton (Derivation A B ℂ) :=
    (KaehlerDifferential.linearMapEquivDerivation A B).surjective.subsingleton
  intro b
  exact congrArg (fun d : Derivation A B ℂ => d b) (Subsingleton.elim d 0)

/-- Differentials of regular functions separate tangent vectors in the
constructed affine charts, including charts with localized coordinates. -/
theorem affineRegularChart_tangent_eq_zero
    {B : Type*} [CommRing B] [Algebra ℂ B] {n : ℕ}
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (v : Fin n → ℂ)
    (hv : ∀ b, fderiv ℂ (fun z => e.symm z b) (e x) v = 0) : v = 0 := by
  have hd (b : B) : DifferentiableAt ℂ (fun z => e.symm z b) (e x) :=
    ((he.1 b).contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
      (by simp)
  obtain ⟨g, hg, hcoords⟩ := he.2
  funext i
  obtain ⟨b, k, hk⟩ := hcoords i
  have hnz : e.symm (e x) g ≠ 0 := by
    rw [e.left_inv hx]
    exact hg x hx
  have heq : (fun z => e.symm z b) =ᶠ[𝓝 (e x)]
      (fun z => z i * (e.symm z g) ^ k) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with z hz
    have h := hk (e.symm z) (e.map_target hz)
    rw [e.right_inv hz] at h
    exact ((eq_div_iff (pow_ne_zero k (hg _ (e.map_target hz)))).mp h).symm
  have hdiff := congrArg (fun L : (Fin n → ℂ) →L[ℂ] ℂ => L v) heq.fderiv_eq
  have hmul := fderiv_fun_mul (hasFDerivAt_apply i (e x)).differentiableAt ((hd g).pow k)
  simp only [Pi.pow_apply] at hmul
  rw [hmul, fderiv_pow k (hd g), (hasFDerivAt_apply i (e x)).fderiv] at hdiff
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, hv, smul_eq_mul, mul_zero, zero_add] at hdiff
  exact (mul_eq_zero.mp hdiff.symm).resolve_left (pow_ne_zero k hnz)

/-- A formally unramified algebra map has injective analytic differential
in any pair of the established regular charts. -/
theorem fderiv_affineChartComap_injective_of_unramified
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    {n m : ℕ} (h : A →ₐ[ℂ] B) (hh : h.toRingHom.FormallyUnramified)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (Fin n → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B n) (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source)
    (hfx : x.comp h ∈ f.source) :
    Function.Injective (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hd (b : B) : DifferentiableAt ℂ (fun z => e.symm z b) (e x) :=
    ((he.1 b).contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
      (by simp)
  let D : B → ℂ := fun b => fderiv ℂ (fun z => e.symm z b) (e x) v
  apply affineRegularChart_tangent_eq_zero e he x hx v
  apply point_derivation_eq_zero_of_unramified h hh x D
  · intro a b
    dsimp [D]
    simp only [map_add]
    rw [fderiv_fun_add (hd a) (hd b), add_apply]
  · intro a b
    dsimp [D]
    simp only [map_mul]
    rw [fderiv_fun_mul (hd a) (hd b)]
    simp only [add_apply, smul_apply,
      e.left_inv hx, smul_eq_mul]
  · intro a
    have heq : (fun z => e.symm z (h a)) =ᶠ[𝓝 (e x)]
        (fun z => f.symm (f ((e.symm z).comp h)) a) := by
      filter_upwards [ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood h e f x hx hfx] with z hz
      rw [f.left_inv hz.2]
      rfl
    have hF := (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx).differentiableAt
      (by simp)
    have hfa : DifferentiableAt ℂ (fun w => f.symm w a)
        (f ((e.symm (e x)).comp h)) := by
      rw [e.left_inv hx]
      exact ((hf.1 a).contDiffAt
        (f.open_target.mem_nhds (f.map_source hfx))).differentiableAt (by simp)
    change fderiv ℂ (fun z => e.symm z (h a)) (e x) v = 0
    have hchain := fderiv_comp (e x) hfa hF
    simp only [Function.comp_def] at hchain
    rw [heq.fderiv_eq, hchain,
      ContinuousLinearMap.comp_apply, hv, map_zero]

/-- The preceding chart computation gives the actual native manifold
differential of an unramified map of smooth affine complex varieties. -/
theorem mfderiv_smoothDomain_comap_injective_of_unramified
    {A B : Type*} [CommRing A] [Algebra ℂ A] [IsDomain A] [Algebra.Smooth ℂ A]
    [CommRing B] [Algebra ℂ B] [IsDomain B] [Algebra.Smooth ℂ B]
    (h : A →ₐ[ℂ] B) (hh : h.toRingHom.FormallyUnramified) (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) :
    Function.Injective
      (mfderiv (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
        (𝓘(ℂ, Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ))
        (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.comap h) x) := by
  rw [ComplexPoints.Analytic.SmoothClosedImmersion.mfderiv_smoothDomain_comap_eq_chart_fderiv]
  exact fderiv_affineChartComap_injective_of_unramified h hh
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ) x)
    (chartAt (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ A) → ℂ) (x.comp h))
    (chart_mem_atlas _ x) (chart_mem_atlas _ (x.comp h)) x
    (mem_chart_source _ x) (mem_chart_source _ (x.comp h))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.EtaleDifferential.Constructions.Construction
