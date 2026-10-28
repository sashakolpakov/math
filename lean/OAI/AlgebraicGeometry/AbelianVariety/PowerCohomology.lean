import OAI.AlgebraicGeometry.AbelianVariety.DeRham
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality

/-! # Power Cohomology -/

namespace OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology.Constructions.Exterior

noncomputable section

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Group G] [TopologicalSpace G] [ChartedSpace E G]
  [LieGroup 𝓘(ℝ, E) ∞ G] {n : ℕ}

theorem hom_pullback_mem_invariantForms (f : G → G)
    (hmul : ∀ x y, f (x * y) = f x * f y)
    (hs : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback f hs form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n := by
  rw [InvariantClosed.Constructions.ExteriorCohomology.mem_invariantForms_iff] at hf ⊢
  intro g
  have he : f ∘ (fun x : G => g * x) = (fun x : G => f g * x) ∘ f := by
    funext x
    exact hmul g x
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  simp only [he]
  have hp := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp f hs (fun x : G => f g * x)
    (contMDiff_mul_left (I := 𝓘(ℝ, E)) (n := ∞)) form
  rw [hf (f g)] at hp
  exact hp

theorem pow_pullback_one (k : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => x ^ k)
      (contMDiff_pow (I := 𝓘(ℝ, E)) (n := ∞) k) form) 1 = (k : ℂ) ^ n • form 1 := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_apply, one_pow]
  ext v
  change (form 1) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : G => x ^ k) 1 (v i)) =
    (k : ℂ) ^ n * (form 1) v
  have hs := (form 1).toAlternatingMap.map_smul_univ (fun _ : Fin n => (k : ℝ)) v
  have he : (fun i : Fin n => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : G => x ^ k) 1 (v i)) =
      (fun i => (k : ℝ) • v i) := by
    funext i
    exact PowerLie.Constructions.ExteriorCohomology.mfderiv_pow_one (E := E) (G := G) k (v i)
  exact (congrArg (form 1) he).trans (by simpa using hs)

variable [IsMulCommutative G]

theorem pow_pullback_invariant (k : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E G n)
    (hf : form ∈ InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (fun x : G => x ^ k)
      (contMDiff_pow (I := 𝓘(ℝ, E)) (n := ∞) k) form = (k : ℂ) ^ n • form := by
  let lhs : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n :=
    ⟨_, hom_pullback_mem_invariantForms _
      (fun x y => (show Commute x y from mul_comm' x y).mul_pow k)
      (contMDiff_pow (I := 𝓘(ℝ, E)) (n := ∞) k) form hf⟩
  let rhs : InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n :=
    ⟨_, (InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) n).smul_mem ((k : ℂ) ^ n) hf⟩
  have he : lhs = rhs := (InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv n).injective (pow_pullback_one k form)
  exact congrArg Subtype.val he

theorem abelianPower_deRham (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k n : ℕ)
    (a : A.variety.deRhamCohomology n) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n a =
      (k : ℂ) ^ n • a := by
  obtain ⟨form, rfl⟩ := (DeRham.Constructions.ExteriorCohomology.abelianInvariantDeRhamEquiv A n).surjective a
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k))
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) ∞) n
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass _ _ n (InvariantCohomology.Constructions.Exterior.invariantClosedInclusion n form)) = _
  rw [Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply]
  have he : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) =
      (fun x : A.variety.analyticSpace => x ^ k) := funext (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism_point A k)
  have hp : Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k))
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) ∞) n
      (InvariantCohomology.Constructions.Exterior.invariantClosedInclusion n form) = (k : ℂ) ^ n • InvariantCohomology.Constructions.Exterior.invariantClosedInclusion n form := by
    apply Subtype.ext
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback _ _ form.val = (k : ℂ) ^ n • form.val
    simp only [he]
    exact pow_pullback_invariant k form.val form.property
  rw [hp, map_smul]
  rfl

theorem abelianPower_complexBetti (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k n : ℕ)
    (a : A.variety.complexCohomology n) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n a =
      (k : ℂ) ^ n • a := by
  obtain ⟨b, rfl⟩ := (A.variety.deRhamBettiIso n).toLinearEquiv.surjective a
  have h := ConcreteCategory.congr_hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n) b
  change _ = (A.variety.deRhamBettiIso n).hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n b) at h
  rw [abelianPower_deRham, map_smul] at h
  exact h

theorem abelianPower_rationalBetti (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (k n : ℕ)
    (a : A.variety.rationalCohomology n) :
    Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n a =
      (k : ℚ) ^ n • a := by
  apply A.variety.rationalCohomologyInclusion_injective n
  have h := ConcreteCategory.congr_hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomologyInclusion_pullback
      (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n) a
  change A.variety.rationalCohomologyInclusion n
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n a) =
      Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback (PowerImage.Constructions.ExteriorCohomology.abelianPowerMorphism A k) n
        (A.variety.rationalCohomologyInclusion n a) at h
  refine h.trans ((abelianPower_complexBetti A k n
    (A.variety.rationalCohomologyInclusion n a)).trans ?_)
  rw [map_smul]
  change (k : ℂ) ^ n • (A.variety.rationalCohomologyInclusion n a) =
    (algebraMap ℚ ℂ ((k : ℚ) ^ n)) • (A.variety.rationalCohomologyInclusion n a)
  simp

end

end OAI.AlgebraicGeometry.AbelianVariety.PowerCohomology.Constructions.Exterior
