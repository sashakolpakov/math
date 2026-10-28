import OAI.AlgebraicTopology.DeRham.Comparison.RelativeSmoothCechComparison
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
import OAI.Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence
import OAI.Analysis.DifferentialForms.Manifold.CechDeRham

/-! # Euclidean Form Cech -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.EuclideanFormCech

noncomputable section

/-!
# The actual relative Čech augmentation for Euclidean manifold forms

The coordinate equivalence between genuine ambient manifold forms and smooth
coefficient forms is natural under open restriction. It therefore transports
the proved smooth-form gluing and partition contractions to the actual
manifold-form Čech rows, for covers of an arbitrary open domain.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual normed-coordinate equivalence is an isomorphism of form presheaves. -/
def localNormedFormPresheafIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E n ≅ Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E n :=
  NatIso.ofComponents (fun U => (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv (unop U) n).toModuleIso) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_restrict (leOfHom f.unop) form)

variable {ι : Type} (U : ι → Opens E)

/-- Actual manifold-form Čech rows identify with coefficient-form Čech rows. -/
def localNormedCechRowIso (q : ℕ) :
    SmoothCech.cechComplex (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q) U ≅ SmoothCech.smoothCechComplex U q :=
  (CechDoubleComplexFunctor.cechComplexFunctor U).mapIso (localNormedFormPresheafIso E q)

@[simp]
theorem localNormedCechRowIso_hom_f_apply (q p : ℕ)
    (c : SmoothCech.CechCochain (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q) U p)
    (a : Fin (p + 1) → ι) :
    ((localNormedCechRowIso E U q).hom.f p c) a =
      Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv (SmoothCech.cechIntersection U a) q (c a) := rfl

variable (W : Opens E) (hsub : ∀ i, U i ≤ W)

/-- The row identification preserves restriction from the actual open domain. -/
theorem localNormedCechRowIso_augmentation (q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E W q) :
    (localNormedCechRowIso E U q).hom.f 0
        ((CechComplexAugmentation.cechColumnAugmentation U W hsub (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).f q form) =
      SmoothCechAugmentation.smoothCechAugmentation U q W hsub (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv W q form) := by
  funext a
  exact Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv_restrict
    (CechComplexAugmentation.cechIntersection_le_openDomain U W hsub a) form

variable (hcover : ∀ x : W, ∃ i, (x : E) ∈ U i)

include hcover in
/-- The actual relative manifold-form column augmentation is injective. -/
theorem euclideanManifoldCechColumnAugmentation_injective (q : ℕ) :
    Function.Injective
      ((CechComplexAugmentation.cechColumnAugmentation U W hsub (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).f q) := by
  intro form other h
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E W q at form other
  apply (Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv W q).injective
  apply SmoothCechAugmentation.smoothCechAugmentation_injective U q W hsub
    (fun x hx => Set.mem_iUnion.mpr (hcover ⟨x, hx⟩))
  exact (localNormedCechRowIso_augmentation E U W hsub q form).symm.trans
    ((congrArg ((localNormedCechRowIso E U q).hom.f 0) h).trans
      (localNormedCechRowIso_augmentation E U W hsub q other))

include hcover in
/-- The actual relative manifold-form augmentation has image equal to zero Čech cocycles. -/
theorem euclideanManifoldCechColumnAugmentation_exact (q : ℕ) :
    Function.Exact
      ((CechComplexAugmentation.cechColumnAugmentation U W hsub (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).f q)
      (((CechDoubleComplexFunctor.cechDoubleComplex U (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).d 0 1).f q) := by
  rw [CechDoubleComplexFunctor.cechDoubleComplex_d_f, CechComplexAugmentation.cechColumnAugmentation_f]
  change Function.Exact (CechComplexAugmentation.cechSectionAugmentation U W hsub (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q))
    (SmoothCech.cechDelta (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q) U 0)
  intro c
  constructor
  · intro hc
    have hcs : SmoothCech.smoothCechDelta U q 0 ((localNormedCechRowIso E U q).hom.f 0 c) = 0 := by
      have h := ConcreteCategory.congr_hom ((localNormedCechRowIso E U q).hom.comm 0 1) c
      rw [SmoothCech.cechComplex_d, SmoothCech.cechComplex_d] at h
      change SmoothCech.smoothCechDelta U q 0 ((localNormedCechRowIso E U q).hom.f 0 c) =
        (localNormedCechRowIso E U q).hom.f 1
          (SmoothCech.cechDelta (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q) U 0 c) at h
      exact h.trans ((congrArg ((localNormedCechRowIso E U q).hom.f 1) hc).trans
        (map_zero ((localNormedCechRowIso E U q).hom.f 1).hom))
    obtain ⟨form, hform⟩ :=
      (SmoothCechComparison.smoothCechColumnAugmentation_exact U W hsub
        (fun x hx => Set.mem_iUnion.mpr (hcover ⟨x, hx⟩)) q
        ((localNormedCechRowIso E U q).hom.f 0 c)).mp hcs
    change Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm W q at form
    refine ⟨(Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv W q).symm form, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso ((localNormedCechRowIso E U q).hom.f 0)).1
    change (localNormedCechRowIso E U q).hom.f 0
        ((CechComplexAugmentation.cechColumnAugmentation U W hsub (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).f q
          ((Analysis.DifferentialForms.Manifold.LocalNormedFormEquivalence.localNormedFormEquiv W q).symm form)) = _
    rw [localNormedCechRowIso_augmentation, LinearEquiv.apply_symm_apply]
    exact hform
  · rintro ⟨form, rfl⟩
    exact CechComplexAugmentation.cechSectionAugmentation_delta U W hsub (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E E q) form

variable [FiniteDimensional ℝ E]

include hsub hcover in
/-- The proved relative partition contraction gives positive exactness for the actual rows. -/
theorem euclideanManifoldCechRow_exactAt (p q : ℕ) :
    ((CechDoubleComplexFunctor.cechDoubleComplex U (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)).flip.X q).ExactAt (p + 1) := by
  rw [CechDoubleComplexFunctor.cechDoubleComplex_row]
  have h : (SmoothCech.smoothCechComplex U q).ExactAt (p + 1) := by
    simpa only [SmoothCechDoubleComplex.smoothCechDoubleComplex_row] using
      RelativeSmoothCechComparison.relativeSmoothCechRow_exactAt W U hsub hcover p q
  exact h.of_iso (localNormedCechRowIso E U q).symm

include hcover in
/-- For every open cover of an arbitrary Euclidean open domain, the actual
generic manifold-form augmentation is a quasi-isomorphism. -/
theorem euclideanManifoldCechAugmentation_quasiIso :
    QuasiIso (CechComplexAugmentation.cechTotalAugmentation U W hsub (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldDeRhamPresheafComplex E E)) := by
  unfold CechComplexAugmentation.cechTotalAugmentation
  apply DoubleComplexComparison.DoubleComplex.augmentationToTotal_quasiIso
  · exact euclideanManifoldCechColumnAugmentation_injective E U W hsub hcover
  · exact euclideanManifoldCechColumnAugmentation_exact E U W hsub hcover
  · exact euclideanManifoldCechRow_exactAt E U W hsub hcover

end

end OAI.AlgebraicTopology.DeRham.Comparison.EuclideanFormCech
