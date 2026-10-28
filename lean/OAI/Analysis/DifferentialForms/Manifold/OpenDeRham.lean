import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Open De Rham -/

namespace OAI.Analysis.DifferentialForms.Manifold.OpenDeRham

noncomputable section

/-!
# De Rham complexes of manifold forms on open domains

These are complexes of actual smooth sections of the alternating cotangent
bundle over open subsets of a smooth real manifold. The constructed local
exterior derivative commutes with restrictions, giving both a presheaf of
cochain complexes and a presheaf of cohomology modules. No exactness or
sheaf property of the cohomology presheaf is asserted.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u v

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {U V W : Opens M}

/-- The de Rham complex of genuine smooth manifold forms on an open domain. -/
def openManifoldDeRhamComplex (U : Opens M) :
    CochainComplex (ModuleCat.{max u v} ℂ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U n))
    (fun _ => ModuleCat.ofHom Open.SmoothOpenManifoldForm.d)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext Open.SmoothOpenManifoldForm.d_squared))

@[simp]
theorem openManifoldDeRhamComplex_X (U : Opens M) (n : ℕ) :
    (openManifoldDeRhamComplex E U).X n =
      ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U n) := rfl

@[simp]
theorem openManifoldDeRhamComplex_d (U : Opens M) (n : ℕ) :
    (openManifoldDeRhamComplex E U).d n (n + 1) = ModuleCat.ofHom
      (Open.SmoothOpenManifoldForm.d :
        Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Open.SmoothOpenManifoldForm E U (n + 1)) := by
  exact CochainComplex.of_d
    (fun k => ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U k))
    (fun k => ModuleCat.ofHom (Open.SmoothOpenManifoldForm.d :
      Open.SmoothOpenManifoldForm E U k →ₗ[ℂ] Open.SmoothOpenManifoldForm E U (k + 1))) n

/-- Restriction of local manifold forms is a cochain map. -/
def openManifoldDeRhamRestrict (h : V ≤ U) :
    openManifoldDeRhamComplex E U ⟶ openManifoldDeRhamComplex E V :=
  CochainComplex.ofHom
    (fun _ => ModuleCat.ofHom (Open.SmoothOpenManifoldForm.restrict h))
    (fun n => by
      rw [openManifoldDeRhamComplex_d, openManifoldDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact (Open.SmoothOpenManifoldForm.restrict_d h form).symm)

@[simp]
theorem openManifoldDeRhamRestrict_f_apply (h : V ≤ U) (n : ℕ)
    (form : Open.SmoothOpenManifoldForm E U n) :
    (openManifoldDeRhamRestrict E h).f n form =
      Open.SmoothOpenManifoldForm.restrict h form := rfl

@[simp]
theorem openManifoldDeRhamRestrict_refl (U : Opens M) :
    openManifoldDeRhamRestrict E (le_refl U) =
      𝟙 (openManifoldDeRhamComplex E U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Open.SmoothOpenManifoldForm.restrict_refl form

theorem openManifoldDeRhamRestrict_comp (hVU : V ≤ U) (hWV : W ≤ V) :
    openManifoldDeRhamRestrict E (hWV.trans hVU) =
      openManifoldDeRhamRestrict E hVU ≫ openManifoldDeRhamRestrict E hWV := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact (Open.SmoothOpenManifoldForm.restrict_trans hVU hWV form).symm

/-- The actual de Rham cohomology of smooth manifold forms over an open set. -/
def openManifoldDeRhamCohomology (U : Opens M) (n : ℕ) : ModuleCat.{max u v} ℂ :=
  (openManifoldDeRhamComplex E U).homology n

/-- Restriction on the de Rham cohomology of open manifold domains. -/
def openManifoldDeRhamCohomologyRestrict (h : V ≤ U) (n : ℕ) :
    openManifoldDeRhamCohomology E U n ⟶ openManifoldDeRhamCohomology E V n :=
  HomologicalComplex.homologyMap (openManifoldDeRhamRestrict E h) n

@[simp]
theorem openManifoldDeRhamCohomologyRestrict_refl (U : Opens M) (n : ℕ) :
    openManifoldDeRhamCohomologyRestrict E (le_refl U) n =
      𝟙 (openManifoldDeRhamCohomology E U n) := by
  change HomologicalComplex.homologyMap
    (openManifoldDeRhamRestrict E (le_refl U)) n =
      𝟙 ((openManifoldDeRhamComplex E U).homology n)
  rw [openManifoldDeRhamRestrict_refl, HomologicalComplex.homologyMap_id]

theorem openManifoldDeRhamCohomologyRestrict_comp
    (hVU : V ≤ U) (hWV : W ≤ V) (n : ℕ) :
    openManifoldDeRhamCohomologyRestrict E (hWV.trans hVU) n =
      openManifoldDeRhamCohomologyRestrict E hVU n ≫
        openManifoldDeRhamCohomologyRestrict E hWV n := by
  change HomologicalComplex.homologyMap
      (openManifoldDeRhamRestrict E (hWV.trans hVU)) n =
    HomologicalComplex.homologyMap (openManifoldDeRhamRestrict E hVU) n ≫
      HomologicalComplex.homologyMap (openManifoldDeRhamRestrict E hWV) n
  rw [openManifoldDeRhamRestrict_comp, HomologicalComplex.homologyMap_comp]

variable (M) in
/-- The presheaf of de Rham cochain complexes on a smooth real manifold. -/
def openManifoldDeRhamPresheaf :
    (Opens M)ᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} ℂ) ℕ where
  obj U := openManifoldDeRhamComplex E (unop U)
  map f := openManifoldDeRhamRestrict E (leOfHom f.unop)
  map_id U := openManifoldDeRhamRestrict_refl E (unop U)
  map_comp f g := openManifoldDeRhamRestrict_comp E (leOfHom f.unop) (leOfHom g.unop)

variable (M) in
/-- The presheaf obtained by taking de Rham cohomology over every open domain. -/
def openManifoldDeRhamCohomologyPresheaf (n : ℕ) :
    (Opens M)ᵒᵖ ⥤ ModuleCat.{max u v} ℂ :=
  openManifoldDeRhamPresheaf E M ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Restriction of global manifold forms to an open domain is a cochain map. -/
def manifoldDeRhamOnOpen (U : Opens M) :
    ManifoldDeRham.manifoldDeRhamComplex E M ⟶ openManifoldDeRhamComplex E U :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom (Algebra.SmoothManifoldForm.onOpen U))
    (fun n => by
      rw [ManifoldDeRham.manifoldDeRhamComplex_d, openManifoldDeRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact Algebra.SmoothManifoldForm.onOpen_d U form)

@[simp]
theorem manifoldDeRhamOnOpen_f_apply (U : Opens M) (n : ℕ)
    (form : Algebra.SmoothManifoldForm E M n) :
    (manifoldDeRhamOnOpen E U).f n form = Algebra.SmoothManifoldForm.onOpen U form := rfl

theorem manifoldDeRhamOnOpen_restrict (h : V ≤ U) :
    manifoldDeRhamOnOpen E U ≫ openManifoldDeRhamRestrict E h =
      manifoldDeRhamOnOpen E V := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Algebra.SmoothManifoldForm.restrict_onOpen h form

/-- The induced restriction of global manifold de Rham cohomology. -/
def manifoldDeRhamCohomologyOnOpen (U : Opens M) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology E M n ⟶ openManifoldDeRhamCohomology E U n :=
  HomologicalComplex.homologyMap (manifoldDeRhamOnOpen E U) n

theorem manifoldDeRhamCohomologyOnOpen_restrict (h : V ≤ U) (n : ℕ) :
    manifoldDeRhamCohomologyOnOpen E U n ≫
        openManifoldDeRhamCohomologyRestrict E h n =
      manifoldDeRhamCohomologyOnOpen E V n := by
  change HomologicalComplex.homologyMap (manifoldDeRhamOnOpen E U) n ≫
    HomologicalComplex.homologyMap (openManifoldDeRhamRestrict E h) n =
      HomologicalComplex.homologyMap (manifoldDeRhamOnOpen E V) n
  rw [← HomologicalComplex.homologyMap_comp, manifoldDeRhamOnOpen_restrict]

end

end OAI.Analysis.DifferentialForms.Manifold.OpenDeRham
