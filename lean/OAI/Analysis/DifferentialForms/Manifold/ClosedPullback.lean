import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback
import OAI.Analysis.DifferentialForms.Manifold.ClassRepresentatives

/-! # Closed Pullback -/

namespace OAI.Analysis.DifferentialForms.Manifold.ClosedPullback

noncomputable section

/-!
Pullback on actual closed forms and on their quotient by exact forms, together
with its agreement with the categorical manifold de Rham class map.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

universe u v

variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N P : Type v}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ, G) ∞ P]

/-- Pullback restricted to genuine closed smooth manifold forms. -/
def manifoldClosedFormsPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldClosedForms F N n →ₗ[ℂ] ManifoldDeRham.manifoldClosedForms E M n where
  toFun form := ⟨Algebra.SmoothManifoldForm.pullback f hf form.val, by
    change Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.pullback f hf form.val) = 0
    rw [Algebra.SmoothManifoldForm.d_pullback, form.property, map_zero]⟩
  map_add' form other := by
    apply Subtype.ext
    exact map_add (Algebra.SmoothManifoldForm.pullback f hf) form.val other.val
  map_smul' c form := by
    apply Subtype.ext
    exact map_smul (Algebra.SmoothManifoldForm.pullback f hf) c form.val

@[simp]
theorem manifoldClosedFormsPullback_coe (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : ManifoldDeRham.manifoldClosedForms F N n) :
    (manifoldClosedFormsPullback f hf n form : Algebra.SmoothManifoldForm E M n) =
      Algebra.SmoothManifoldForm.pullback f hf form.val := rfl

@[simp]
theorem manifoldClosedFormsPullback_id (n : ℕ) (form : ManifoldDeRham.manifoldClosedForms E M n) :
    manifoldClosedFormsPullback (id : M → M) (contMDiff_id (I := 𝓘(ℝ, E))) n form = form := by
  apply Subtype.ext
  exact Algebra.SmoothManifoldForm.pullback_id form.val

theorem manifoldClosedFormsPullback_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) (n : ℕ)
    (form : ManifoldDeRham.manifoldClosedForms G P n) :
    manifoldClosedFormsPullback (g ∘ f) (hg.comp hf) n form =
      manifoldClosedFormsPullback f hf n (manifoldClosedFormsPullback g hg n form) := by
  apply Subtype.ext
  exact Algebra.SmoothManifoldForm.pullback_comp f hf g hg form.val

/-- Naturality also holds for the incoming differential in degree zero. -/
theorem manifoldIncomingExteriorDerivative_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : Algebra.SmoothManifoldForm F N (n - 1)) :
    ManifoldDeRham.manifoldIncomingExteriorDerivative E M n (Algebra.SmoothManifoldForm.pullback f hf form) =
      Algebra.SmoothManifoldForm.pullback f hf (ManifoldDeRham.manifoldIncomingExteriorDerivative F N n form) := by
  cases n with
  | zero => simp
  | succ n => exact Algebra.SmoothManifoldForm.d_pullback f hf form

/-- Pullback of the boundary represented by a primitive is the boundary of
the pulled-back primitive. -/
theorem manifoldClosedFormsPullback_boundary (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : Algebra.SmoothManifoldForm F N (n - 1)) :
    manifoldClosedFormsPullback f hf n (ManifoldDeRham.manifoldBoundaryToClosed F N n form) =
      ManifoldDeRham.manifoldBoundaryToClosed E M n (Algebra.SmoothManifoldForm.pullback f hf form) := by
  apply Subtype.ext
  exact (manifoldIncomingExteriorDerivative_pullback f hf n form).symm

theorem manifoldClosedFormsPullback_preserves_exact (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldExactClosedForms F N n ≤
      (ManifoldDeRham.manifoldExactClosedForms E M n).comap (manifoldClosedFormsPullback f hf n) := by
  rintro _ ⟨form, rfl⟩
  exact ⟨Algebra.SmoothManifoldForm.pullback f hf form,
    (manifoldClosedFormsPullback_boundary f hf n form).symm⟩

/-- The induced pullback on the literal quotient of closed forms by exact forms. -/
def manifoldDeRhamFormQuotientPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamFormQuotient F N n →ₗ[ℂ] ManifoldDeRham.manifoldDeRhamFormQuotient E M n :=
  (ManifoldDeRham.manifoldExactClosedForms F N n).mapQ (ManifoldDeRham.manifoldExactClosedForms E M n)
    (manifoldClosedFormsPullback f hf n) (manifoldClosedFormsPullback_preserves_exact f hf n)

@[simp]
theorem manifoldDeRhamFormQuotientPullback_mkQ (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : ManifoldDeRham.manifoldClosedForms F N n) :
    manifoldDeRhamFormQuotientPullback f hf n ((ManifoldDeRham.manifoldExactClosedForms F N n).mkQ form) =
      (ManifoldDeRham.manifoldExactClosedForms E M n).mkQ (manifoldClosedFormsPullback f hf n form) := rfl

/-- The canonical cocycle identification retains the underlying actual form. -/
theorem manifoldDeRhamClosedFormsIso_hom_subtype (n : ℕ) :
    (ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom ≫
      ModuleCat.ofHom (ManifoldDeRham.manifoldClosedForms E M n).subtype =
        (ManifoldDeRham.manifoldDeRhamComplex E M).iCycles n := by
  change (ShortComplex.cyclesMap (ManifoldDeRham.manifoldDeRhamFormShortComplexIso E M n).hom ≫
      (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatCyclesIso.hom) ≫
        (ManifoldDeRham.manifoldFormShortComplex E M n).moduleCatLeftHomologyData.i = _
  rw [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i]
  change ((ManifoldDeRham.manifoldDeRhamComplex E M).sc n).iCycles ≫ 𝟙 _ = _
  exact Category.comp_id _

theorem manifoldDeRhamClosedFormsIso_hom_coe (n : ℕ)
    (cycle : ManifoldDeRham.manifoldDeRhamCocycles E M n) :
    ((ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom cycle : Algebra.SmoothManifoldForm E M n) =
      (ManifoldDeRham.manifoldDeRhamComplex E M).iCycles n cycle :=
  congrArg (fun map : ManifoldDeRham.manifoldDeRhamCocycles E M n ⟶
    ModuleCat.of ℂ (Algebra.SmoothManifoldForm E M n) => map cycle)
      (manifoldDeRhamClosedFormsIso_hom_subtype (E := E) (M := M) n)

/-- Categorical cocycle pullback is exactly pullback of actual closed forms. -/
theorem manifoldDeRhamClosedFormsIso_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ManifoldDeRhamPullback.manifoldDeRhamCocyclesPullback f hf n ≫ (ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom =
      (ClassRepresentatives.manifoldDeRhamClosedFormsIso F N n).hom ≫
        ModuleCat.ofHom (manifoldClosedFormsPullback f hf n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro cycle
  apply Subtype.ext
  change ((ClassRepresentatives.manifoldDeRhamClosedFormsIso E M n).hom
      (ManifoldDeRhamPullback.manifoldDeRhamCocyclesPullback f hf n cycle) : Algebra.SmoothManifoldForm E M n) =
    Algebra.SmoothManifoldForm.pullback f hf
      ((ClassRepresentatives.manifoldDeRhamClosedFormsIso F N n).hom cycle : Algebra.SmoothManifoldForm F N n)
  rw [manifoldDeRhamClosedFormsIso_hom_coe, manifoldDeRhamClosedFormsIso_hom_coe]
  exact congrArg (fun map : (ManifoldDeRham.manifoldDeRhamComplex F N).cycles n ⟶
    (ManifoldDeRham.manifoldDeRhamComplex E M).X n => map cycle)
      (HomologicalComplex.cyclesMap_i (ManifoldDeRhamPullback.manifoldDeRhamPullback f hf) n)

/-- Taking the class of a literal closed form commutes with pullback. -/
theorem manifoldDeRhamFormClass_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass F N n) ≫
      ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f hf n =
    ModuleCat.ofHom (manifoldClosedFormsPullback f hf n) ≫
      ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass E M n) := by
  apply (cancel_epi (ClassRepresentatives.manifoldDeRhamClosedFormsIso F N n).hom).mp
  rw [← Category.assoc, ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class,
    ManifoldDeRhamPullback.manifoldDeRhamClass_pullback, ← ClassRepresentatives.manifoldDeRhamClosedFormsIso_comp_class,
    ← Category.assoc, manifoldDeRhamClosedFormsIso_pullback, Category.assoc]

/-- Evaluation of the naturality identity on an actual closed-form representative. -/
theorem manifoldDeRhamFormClass_pullback_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ)
    (form : ManifoldDeRham.manifoldClosedForms F N n) :
    ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f hf n (ManifoldDeRham.manifoldDeRhamFormClass F N n form) =
      ManifoldDeRham.manifoldDeRhamFormClass E M n (manifoldClosedFormsPullback f hf n form) :=
  congrArg (fun map : ModuleCat.of ℂ (ManifoldDeRham.manifoldClosedForms F N n) ⟶
    ManifoldDeRham.manifoldDeRhamCohomology E M n => map form) (manifoldDeRhamFormClass_pullback f hf n)

/-- The categorical and literal-quotient constructions give the same pullback. -/
theorem manifoldDeRhamFormQuotientIso_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (n : ℕ) :
    (ManifoldDeRham.manifoldDeRhamFormQuotientIso F N n).hom ≫
      ModuleCat.ofHom (manifoldDeRhamFormQuotientPullback f hf n) =
    ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback f hf n ≫ (ManifoldDeRham.manifoldDeRhamFormQuotientIso E M n).hom := by
  have : Epi (ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass F N n)) :=
    (ModuleCat.epi_iff_surjective _).mpr (ClassRepresentatives.manifoldDeRhamFormClass_surjective F N n)
  apply (cancel_epi (ModuleCat.ofHom (ManifoldDeRham.manifoldDeRhamFormClass F N n))).mp
  rw [← Category.assoc, ClassRepresentatives.manifoldDeRhamFormClass_comp_quotientIso]
  rw [← Category.assoc, manifoldDeRhamFormClass_pullback, Category.assoc,
    ClassRepresentatives.manifoldDeRhamFormClass_comp_quotientIso]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  rfl

@[simp]
theorem manifoldDeRhamFormQuotientPullback_id (n : ℕ) :
    manifoldDeRhamFormQuotientPullback (id : M → M) (contMDiff_id (I := 𝓘(ℝ, E))) n =
      LinearMap.id := by
  apply LinearMap.ext
  intro cohomologyClass
  obtain ⟨form, rfl⟩ := (ManifoldDeRham.manifoldExactClosedForms E M n).mkQ_surjective cohomologyClass
  rw [manifoldDeRhamFormQuotientPullback_mkQ, manifoldClosedFormsPullback_id]
  rfl

theorem manifoldDeRhamFormQuotientPullback_comp (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) (g : N → P)
    (hg : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, G) ∞ g) (n : ℕ) :
    manifoldDeRhamFormQuotientPullback (g ∘ f) (hg.comp hf) n =
      (manifoldDeRhamFormQuotientPullback f hf n).comp
        (manifoldDeRhamFormQuotientPullback g hg n) := by
  apply LinearMap.ext
  intro cohomologyClass
  obtain ⟨form, rfl⟩ := (ManifoldDeRham.manifoldExactClosedForms G P n).mkQ_surjective cohomologyClass
  simp only [LinearMap.comp_apply, manifoldDeRhamFormQuotientPullback_mkQ]
  exact congrArg (ManifoldDeRham.manifoldExactClosedForms E M n).mkQ
    (manifoldClosedFormsPullback_comp f hf g hg n form)

end

end OAI.Analysis.DifferentialForms.Manifold.ClosedPullback
