import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCovectors
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.SpanningSubfamily
import OAI.AlgebraicGeometry.Comparison.Betti.LinearNormalCoordinates

/-! # Closed Normal Coordinates -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCoordinates

noncomputable section

/-! Finite equations from the original affine kernel complete a local holomorphic left inverse to coordinates. -/

open scoped ContDiff _root_.Topology

open Filter

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
  [IsDomain B] [Algebra.Smooth ℂ B] {m : ℕ}

theorem affineClosed_exists_normalCoordinates
    (h : A →ₐ[ℂ] B) (hh : Function.Surjective h)
    (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints B)
      (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ))
    (f : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (Fin m → ℂ))
    (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas B (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B))
    (hf : f ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas A m)
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) (hx : x ∈ e.source) (hfx : x.comp h ∈ f.source) :
    ∃ (k : ℕ) (a : Fin k → RingHom.ker h.toRingHom)
      (Ψ : (Fin m → ℂ) → (Fin (Foundations.Scheme.SmoothDomainDimension.Algebraic.genericDifferentialRank ℂ B) → ℂ)),
      let q := fun w => (Ψ w, fun i => f.symm w (a i))
      ContDiffAt ℂ ω q (f (x.comp h)) ∧
      Function.Bijective (fderiv ℂ q (f (x.comp h))) ∧
      (fun u => q (f ((e.symm u).comp h))) =ᶠ[𝓝 (e x)] (fun u => (u, 0)) := by
  obtain ⟨Ψ, hΨ, hleft⟩ := ComplexPoints.Analytic.SmoothClosedImmersion.exists_affineChartComap_localLeftInverse h hh e f he hf x hx hfx
  let L := (fderiv ℂ (fun z => f ((e.symm z).comp h)) (e x)).toLinearMap
  obtain ⟨k, b, a, ha⟩ := Finite.SpanningSubfamily.LinearAlgebra.exists_fin_basis_subfamily_of_span_eq
    (LinearMap.range L).dualAnnihilator
    (fun a : RingHom.ker h.toRingHom => ChartCotangentRealization.affineChartRegularDifferential f (x.comp h) a)
    (ClosedNormalCovectors.affineClosedNormalCovectors_span h hh e f he hf x hx hfx)
  let q := fun w => (Ψ w, fun i => f.symm w (a i))
  have hreg (i : Fin k) : ContDiffAt ℂ ω (fun w => f.symm w (a i)) (f (x.comp h)) :=
    (hf.1 (a i)).contDiffAt (f.open_target.mem_nhds (f.map_source hfx))
  have hq : ContDiffAt ℂ ω q (f (x.comp h)) :=
    hΨ.prodMk (contDiffAt_pi.mpr hreg)
  refine ⟨k, a, Ψ, hq, ?_, ?_⟩
  · have hΦ := (ComplexPoints.Analytic.SmoothClosedImmersion.contDiffAt_affineChartComap h e f he hf x hx hfx).differentiableAt (by simp)
    have hΨ' : DifferentiableAt ℂ Ψ (f ((e.symm (e x)).comp h)) := by
      rw [e.left_inv hx]
      exact hΨ.differentiableAt (by simp)
    have hchain := fderiv_comp (e x) hΨ' hΦ
    have hcomp := hleft.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_id] at hcomp
    change fderiv ℂ (fun z => Ψ (f ((e.symm z).comp h))) (e x) = _ at hchain
    rw [hcomp, e.left_inv hx] at hchain
    have hRL : (fderiv ℂ Ψ (f (x.comp h))).toLinearMap.comp L = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact congrArg (fun T => T v) hchain.symm
    have hb := LinearNormalCoordinates.Algebra.linearNormalCoordinates_bijective L
      (fderiv ℂ Ψ (f (x.comp h))).toLinearMap hRL b
    have hderiv : (fderiv ℂ q (f (x.comp h))).toLinearMap =
        (fderiv ℂ Ψ (f (x.comp h))).toLinearMap.prod
          (LinearMap.pi (fun i => (b i : Module.Dual ℂ (Fin m → ℂ)))) := by
      apply LinearMap.ext
      intro v
      apply Prod.ext
      · change (fderiv ℂ q (f (x.comp h)) v).1 = _
        rw [DifferentiableAt.fderiv_prodMk (hΨ.differentiableAt (by simp))
          ((contDiffAt_pi.mpr hreg).differentiableAt (by simp))]
        rfl
      · funext i
        change (fderiv ℂ q (f (x.comp h)) v).2 i = (b i : Module.Dual ℂ (Fin m → ℂ)) v
        rw [DifferentiableAt.fderiv_prodMk (hΨ.differentiableAt (by simp))
          ((contDiffAt_pi.mpr hreg).differentiableAt (by simp)),
          fderiv_pi (fun i => (hreg i).differentiableAt (by simp)), ha]
        rfl
    change Function.Bijective (fderiv ℂ q (f (x.comp h))).toLinearMap
    rw [hderiv]
    exact hb
  · filter_upwards [hleft, ComplexPoints.Analytic.SmoothClosedImmersion.affineChartComap_neighborhood h e f x hx hfx] with u hu hU
    apply Prod.ext
    · exact hu
    · funext i
      change f.symm (f ((e.symm u).comp h)) (a i) = 0
      rw [f.left_inv hU.2]
      change e.symm u (h (a i)) = 0
      have hai : h (a i) = 0 := (a i).property
      rw [hai, map_zero]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.ClosedNormalCoordinates
