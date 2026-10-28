import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses
import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Manifold Pure Classes Pullback -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback

noncomputable section

/-! Holomorphic pullback preserves the actual global pure de Rham images.
The maps are restrictions of canonical pullback on the cohomology of the
genuine smooth manifold form complex. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u v

variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G] [IsScalarTower ℝ ℂ G]
  {M N P : Type v}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℂ, G) ∞ P]

local instance sourceRealManifold : IsManifold 𝓘(ℝ, E) ∞ M :=
  Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

local instance targetRealManifold : IsManifold 𝓘(ℝ, F) ∞ N :=
  Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

local instance thirdRealManifold : IsManifold 𝓘(ℝ, G) ∞ P :=
  Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

/-- Actual holomorphic pullback preserves closed forms of each pure bidegree. -/
theorem manifoldClosedFormsPullback_mem_pureClosed (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms F N (p + q))
    (hform : form ∈ ManifoldPureClasses.pureClosedManifoldForms F N p q) :
    Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form ∈
      ManifoldPureClasses.pureClosedManifoldForms E M p q := by
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q ((form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm F N (p + q)).pullback f)
  exact Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree.pullback hform f hf

/-- Restrict canonical closed-form pullback to the actual pure closed subspaces. -/
def pureClosedManifoldFormsPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ) :
    ManifoldPureClasses.pureClosedManifoldForms F N p q →ₗ[ℂ] ManifoldPureClasses.pureClosedManifoldForms E M p q where
  toFun form := ⟨Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form.val,
    manifoldClosedFormsPullback_mem_pureClosed f hf p q form.val form.property⟩
  map_add' form other := Subtype.ext
    ((Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)).map_add
      form.val other.val)
  map_smul' c form := Subtype.ext
    ((Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)).map_smul
      c form.val)

@[simp]
theorem pureClosedManifoldFormsPullback_coe (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    (form : ManifoldPureClasses.pureClosedManifoldForms F N p q) :
    (pureClosedManifoldFormsPullback f hf p q form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q)) =
      Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form.val := rfl

/-- The actual pure-form class map commutes with holomorphic pullback. -/
theorem manifoldPureFormClass_pullback_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    (form : ManifoldPureClasses.pureClosedManifoldForms F N p q) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)
      (ManifoldPureClasses.manifoldPureFormClass F N p q form) =
        ManifoldPureClasses.manifoldPureFormClass E M p q (pureClosedManifoldFormsPullback f hf p q form) :=
  Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form.val

/-- A class with an actual closed pure representative retains such a representative
under holomorphic pullback. -/
theorem manifoldDeRhamCohomologyPullback_mem_pureImage (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    {classOfForm : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology F N (p + q)}
    (hclass : classOfForm ∈ ManifoldPureClasses.manifoldPureDeRhamImage F N p q) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) classOfForm ∈
      ManifoldPureClasses.manifoldPureDeRhamImage E M p q := by
  obtain ⟨form, hpure, rfl⟩ :=
    (ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff F N p q classOfForm).mp hclass
  apply (ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff E M p q _).mpr
  refine ⟨Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form, ?_, ?_⟩
  · exact manifoldClosedFormsPullback_mem_pureClosed f hf p q form hpure
  · exact (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply f
      (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form).symm

/-- Submodule formulation of preservation of the genuine pure-class image. -/
theorem manifoldPureDeRhamImage_map_pullback_le (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ) :
    (ManifoldPureClasses.manifoldPureDeRhamImage F N p q).map
      (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)).hom ≤
        ManifoldPureClasses.manifoldPureDeRhamImage E M p q := by
  rintro _ ⟨classOfForm, hclass, rfl⟩
  exact manifoldDeRhamCohomologyPullback_mem_pureImage f hf p q hclass

/-- Holomorphic pullback as a linear map between the actual pure-class images. -/
def manifoldPureDeRhamImagePullback (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ) :
    ManifoldPureClasses.manifoldPureDeRhamImage F N p q →ₗ[ℂ] ManifoldPureClasses.manifoldPureDeRhamImage E M p q where
  toFun classOfForm :=
    ⟨Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) classOfForm,
      manifoldDeRhamCohomologyPullback_mem_pureImage f hf p q classOfForm.property⟩
  map_add' left right := Subtype.ext
    ((Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)).hom.map_add
      left.val right.val)
  map_smul' c classOfForm := Subtype.ext
    ((Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q)).hom.map_smul
      c classOfForm.val)

@[simp]
theorem manifoldPureDeRhamImagePullback_coe (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    (classOfForm : ManifoldPureClasses.manifoldPureDeRhamImage F N p q) :
    (manifoldPureDeRhamImagePullback f hf p q classOfForm : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q)) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) classOfForm := rfl

@[simp]
theorem manifoldPureDeRhamImagePullback_id (p q : ℕ) :
    manifoldPureDeRhamImagePullback (id : M → M) (contMDiff_id (I := 𝓘(ℂ, E))) p q =
      LinearMap.id := by
  apply LinearMap.ext
  intro classOfForm
  apply Subtype.ext
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (id : M → M)
    (contMDiff_id (I := 𝓘(ℝ, E))) (p + q) classOfForm.val = classOfForm.val
  simp only [Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback_id, ModuleCat.id_apply]

/-- Restricted pure-class pullback has the usual contravariant composition law. -/
theorem manifoldPureDeRhamImagePullback_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℂ, F) 𝓘(ℂ, G) ∞ g) (p q : ℕ) :
    manifoldPureDeRhamImagePullback (g ∘ f) (hg.comp hf) p q =
      (manifoldPureDeRhamImagePullback f hf p q).comp
        (manifoldPureDeRhamImagePullback g hg p q) := by
  apply LinearMap.ext
  intro classOfForm
  apply Subtype.ext
  exact congrArg (fun map : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology G P (p + q) ⟶
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M (p + q) => map classOfForm.val)
      (Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback_comp f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf)
        g (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hg) (p + q))

/-- The literal closed/exact quotient pure image is also preserved. -/
theorem manifoldDeRhamFormQuotientPullback_mem_pureImage (f : M → N)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f) (p q : ℕ)
    {classOfForm : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient F N (p + q)}
    (hclass : classOfForm ∈ ManifoldPureClasses.manifoldPureQuotientImage F N p q) :
    Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormQuotientPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) classOfForm ∈
      ManifoldPureClasses.manifoldPureQuotientImage E M p q := by
  obtain ⟨form, hpure, rfl⟩ := hclass
  rw [Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormQuotientPullback_mkQ]
  exact ⟨Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) (p + q) form,
    manifoldClosedFormsPullback_mem_pureClosed f hf p q form hpure, rfl⟩

end

end OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback
