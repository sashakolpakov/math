import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDifferential
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelDegrees
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.FormLocalizedCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.ExactLeft

/-! # Added Kernel Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelExactness.ProjectiveCech

noncomputable section

/-! Adding a homogeneous linear coordinate gives an exact kernel in every internal degree. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable [Algebra (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) (MvPolynomial σ R)]
variable (he : ∀ i : σ, algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X (i : WithBot σ)) = X i)
variable (M : Type w) [AddCommGroup M] [Module R M]
  [Module (MvPolynomial (WithBot σ) R) M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial (WithBot σ) R) M] [IsScalarTower R (MvPolynomial σ R) M]
  [IsScalarTower (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) M]
variable (l : MvPolynomial σ R)
variable (hl : algebraMap (MvPolynomial (WithBot σ) R) (MvPolynomial σ R) (X ⊥) = l)
variable (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

include hl in
theorem addedModuleCechKernel_exact (hlhom : l.IsHomogeneous 1) (d : ℤ) (q : ℕ)
    (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M)
    (hf : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d f) (hfc : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f)
    (hker : ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M f = 0)
    (hcycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M f = 0) :
    ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧
      ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M g = 0 ∧ ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f := by
  let E := AddedCechKernel.ProjectiveCech.addedModuleCechComponent R he M l hl
  have hl' : l ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R (1 : ℤ) := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat]
    exact hlhom
  have hEh := AddedKernelDegrees.ProjectiveCech.addedModuleCechComponent_homogeneous R he M l hl ℳ hl' d f hf
  have hEc : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (E f) = 0 := by
    have h := AddedKernelDifferential.ProjectiveCech.addedModuleCechComponent_differential R he M l hl f hker
    rw [hcycle, map_zero] at h
    exact neg_eq_zero.mp h.symm
  have hzero (hfzero : f = 0) : ∃ g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := WithBot σ) R M,
      ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d g ∧ ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧
      ModuleCech.HomogeneousLift.ProjectiveCech.retainedModuleCechMap R Function.Embedding.coeWithBot he M g = 0 ∧ ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g = f := by
    exact ⟨0, fun _ => Submodule.zero_mem _, fun _ _ => rfl, map_zero _, (map_zero _).trans hfzero.symm⟩
  cases q with
  | zero => exact hzero (AddedKernelDegrees.ProjectiveCech.retainedModuleCechMap_kernel_card_zero R he M f hker hfc)
  | succ q =>
    have hEcard := AddedKernelDegrees.ProjectiveCech.addedModuleCechComponent_card R he M l hl q f hfc
    cases q with
    | zero =>
      have hEfzero := Cech.ExactLeft.ProjectiveCech.moduleCechExactAt_zero_vanish R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d
        (Linear.FormLocalizedCech.ProjectiveCech.linearFormLocalized_moduleCechExactAt R M ℳ l hlhom d 0) (E f) hEh hEcard hEc
      apply hzero
      apply AddedCechKernel.ProjectiveCech.addedModuleCechComponent_injective_on_kernel R he M l hl f 0 hker (map_zero _)
      exact hEfzero.trans (map_zero E).symm
    | succ r =>
      have hnEh : ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d (-E f) :=
        fun s => Submodule.neg_mem _ (hEh s)
      have hnEc : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (r + 1) (-E f) := by
        intro s hs
        change -(E f s) = 0
        rw [hEcard s hs, neg_zero]
      have hnCycle : ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (-E f) = 0 := by rw [map_neg, hEc, neg_zero]
      obtain ⟨a, ha, hac, had⟩ := Linear.FormLocalizedCech.ProjectiveCech.linearFormLocalized_moduleCechExactAt R M ℳ l hlhom d (r + 1)
        (-E f) hnEh hnEc hnCycle
      obtain ⟨g, hg⟩ := (AddedCechKernel.ProjectiveCech.addedModuleCechKernelEquiv R he M l hl).surjective a
      change E g.val = a at hg
      refine ⟨g.val, ?_, ?_, g.property, ?_⟩
      · apply (AddedKernelDegrees.ProjectiveCech.addedModuleCechComponent_homogeneous_iff R he M l hl ℳ hl' d g.val g.property).mp
        change ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (Localized.DegreePieces.GradedModules.localizedDegreePiece ℳ l 1) d (E g.val)
        rwa [hg]
      · change ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (r + 1) g.val
        apply (AddedKernelDegrees.ProjectiveCech.addedModuleCechComponent_card_iff R he M l hl r g.val g.property).mp
        change ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R (Presentations.Module.Fractions.GradedModules.AwayModule l M) r (E g.val)
        simpa only [hg, Nat.add_sub_cancel] using hac
      · apply AddedCechKernel.ProjectiveCech.addedModuleCechComponent_injective_on_kernel R he M l hl
          (ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M g.val) f
          (AddedKernelDifferential.ProjectiveCech.retainedModuleCechMap_kernel_differential R he M g.val g.property) hker
        rw [AddedKernelDifferential.ProjectiveCech.addedModuleCechComponent_differential R he M l hl g.val g.property]
        change -ModuleCech.Card.ProjectiveCech.moduleCechDifferential R (Presentations.Module.Fractions.GradedModules.AwayModule l M) (E g.val) = E f
        rw [hg, had, neg_neg]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AddedKernelExactness.ProjectiveCech
