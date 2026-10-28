import OAI.Analysis.DifferentialForms.Manifold.ManifoldGluing
import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Manifold Sheaf -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
The module-valued sheaf of actual smooth manifold differential forms.
Sections are genuine alternating covectors on tangent spaces at each point.
The sheaf condition follows from the proved dependent-section gluing theorem.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

universe u v

/-- The existing additive structure on module presheaves, through the wrapper. -/
instance ManifoldSheaf.complexModulePresheafPreadditiveAny (X : TopCat.{v}) :
    Preadditive (TopCat.Presheaf (ModuleCat.{u} ℂ) X) :=
  inferInstanceAs (Preadditive ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} ℂ))

/-- The existing additive structure on module sheaves, at arbitrary universes. -/
instance ManifoldSheaf.complexModuleSheafPreadditiveAny (X : TopCat.{v}) :
    Preadditive (TopCat.Sheaf (ModuleCat.{u} ℂ) X) :=
  inferInstanceAs (Preadditive
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} ℂ)))

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Type v) [TopologicalSpace M] [ChartedSpace E M]

/-- Smooth local tangent-covector fields and their actual restrictions. -/
def ManifoldSheaf.manifoldFormPresheaf (n : ℕ) :
    TopCat.Presheaf (ModuleCat.{max u v} ℂ) (TopCat.of M) where
  obj U := ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E (unop U) n)
  map h := ModuleCat.ofHom (Open.SmoothOpenManifoldForm.restrict (CategoryTheory.leOfHom h.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Open.SmoothOpenManifoldForm.restrict_refl form
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    rfl

@[simp]
theorem ManifoldSheaf.manifoldFormPresheaf_obj (n : ℕ) (U : Opens M) :
    (ManifoldSheaf.manifoldFormPresheaf E M n).obj (op U) =
      ModuleCat.of ℂ (Open.SmoothOpenManifoldForm E U n) := rfl

@[simp]
theorem ManifoldSheaf.manifoldFormPresheaf_map (n : ℕ) {U V : Opens M} (h : V ≤ U) :
    (ManifoldSheaf.manifoldFormPresheaf E M n).map (homOfLE h).op =
      ModuleCat.ofHom (Open.SmoothOpenManifoldForm.restrict (E := E) h) := rfl

/-- The manifold form presheaf satisfies mathlib's categorical sheaf axiom. -/
theorem ManifoldSheaf.manifoldFormPresheaf_isSheaf (n : ℕ) : (ManifoldSheaf.manifoldFormPresheaf E M n).IsSheaf := by
  let : CategoryTheory.Limits.HasLimitsOfSize.{v, v} (ModuleCat.{max u v} ℂ) :=
    ModuleCat.hasLimitsOfSize.{v, v, max u v, 0} (R := ℂ)
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (ManifoldSheaf.manifoldFormPresheaf E M n)).2
  intro ι U forms hcompat
  have hlocal : Open.SmoothOpenManifoldForm.Compatible forms := by
    apply (Open.SmoothOpenManifoldForm.compatible_iff_restrict forms).2
    intro i j
    exact hcompat i j
  obtain ⟨form, hform, huniq⟩ := Open.SmoothOpenManifoldForm.existsUnique_glue_iSup forms hlocal
  exact ⟨form, hform, huniq⟩

/-- The genuine module-valued sheaf of smooth manifold n-forms. -/
def ManifoldSheaf.manifoldFormSheaf (n : ℕ) :
    TopCat.Sheaf (ModuleCat.{max u v} ℂ) (TopCat.of M) where
  obj := ManifoldSheaf.manifoldFormPresheaf E M n
  property := ManifoldSheaf.manifoldFormPresheaf_isSheaf E M n

@[simp]
theorem ManifoldSheaf.manifoldFormSheaf_presheaf (n : ℕ) :
    (ManifoldSheaf.manifoldFormSheaf E M n).presheaf = ManifoldSheaf.manifoldFormPresheaf E M n := rfl

section

variable {E M} {n : ℕ}

/-- A section on the top open set is an actual global smooth covector field. -/
def Open.SmoothOpenManifoldForm.toGlobal : Open.SmoothOpenManifoldForm E (⊤ : Opens M) n →ₗ[ℂ] Manifold.Algebra.SmoothManifoldForm E M n where
  toFun form := ⟨form.extension, by simpa only [Opens.coe_top] using form.smooth⟩
  map_add' form other := Subtype.ext (Open.SmoothOpenManifoldForm.extension_add form other)
  map_smul' z form := Subtype.ext (Open.SmoothOpenManifoldForm.extension_smul z form)

@[simp]
theorem Open.SmoothOpenManifoldForm.toGlobal_apply (form : Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) (x : M) :
    Open.SmoothOpenManifoldForm.toGlobal form x = form ⟨x, by simp⟩ := Open.SmoothOpenManifoldForm.extension_apply form ⟨x, by simp⟩

@[simp]
theorem Open.SmoothOpenManifoldForm.onOpen_toGlobal (form : Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) :
    Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Open.SmoothOpenManifoldForm.toGlobal form) = form := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  exact Open.SmoothOpenManifoldForm.extension_apply form x

end

section

variable {E M} {n : ℕ}

@[simp]
theorem Algebra.SmoothManifoldForm.toGlobal_onOpen (form : Manifold.Algebra.SmoothManifoldForm E M n) :
    Open.SmoothOpenManifoldForm.toGlobal (Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) = form := by
  apply Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  exact Open.SmoothOpenManifoldForm.extension_apply (Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form) ⟨x, by simp⟩

/-- Global covector fields are exactly the global sections of the local-form sheaf. -/
def Algebra.SmoothManifoldForm.onTopEquiv : Manifold.Algebra.SmoothManifoldForm E M n ≃ₗ[ℂ] Open.SmoothOpenManifoldForm E (⊤ : Opens M) n where
  toLinearMap := Manifold.Algebra.SmoothManifoldForm.onOpen ⊤
  invFun := Open.SmoothOpenManifoldForm.toGlobal
  left_inv := Manifold.Algebra.SmoothManifoldForm.toGlobal_onOpen
  right_inv := Open.SmoothOpenManifoldForm.onOpen_toGlobal

end

/-- The sheaf's global sections recover the original global differential forms. -/
def ManifoldSheaf.manifoldFormGlobalSectionsIso (n : ℕ) :
    (ManifoldSheaf.manifoldFormSheaf E M n).presheaf.obj (op ⊤) ≅
      ModuleCat.of ℂ (Manifold.Algebra.SmoothManifoldForm E M n) :=
  (Manifold.Algebra.SmoothManifoldForm.onTopEquiv (E := E) (M := M) (n := n)).symm.toModuleIso

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Exterior differentiation is natural under restriction of manifold sections. -/
def ManifoldSheaf.manifoldFormPresheafD (n : ℕ) :
    ManifoldSheaf.manifoldFormPresheaf E M n ⟶ ManifoldSheaf.manifoldFormPresheaf E M (n + 1) where
  app U := ModuleCat.ofHom Open.SmoothOpenManifoldForm.d
  naturality U V h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact (Open.SmoothOpenManifoldForm.restrict_d (CategoryTheory.leOfHom h.unop) form).symm

@[simp]
theorem ManifoldSheaf.manifoldFormPresheafD_app (n : ℕ) (U : Opens M) :
    (ManifoldSheaf.manifoldFormPresheafD E M n).app (op U) =
      ModuleCat.ofHom (Open.SmoothOpenManifoldForm.d (E := E) (U := U) (n := n)) := rfl

/-- The presheaf exterior derivative squares to zero. -/
theorem ManifoldSheaf.manifoldFormPresheafD_squared (n : ℕ) :
    ManifoldSheaf.manifoldFormPresheafD E M n ≫ ManifoldSheaf.manifoldFormPresheafD E M (n + 1) = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro form
  exact Open.SmoothOpenManifoldForm.d_squared form

/-- Exterior differentiation as a morphism of the actual manifold form sheaves. -/
def ManifoldSheaf.manifoldFormSheafD (n : ℕ) :
    ManifoldSheaf.manifoldFormSheaf E M n ⟶ ManifoldSheaf.manifoldFormSheaf E M (n + 1) :=
  ObjectProperty.homMk (ManifoldSheaf.manifoldFormPresheafD E M n)

/-- The sheaf exterior derivative squares to zero. -/
theorem ManifoldSheaf.manifoldFormSheafD_squared (n : ℕ) :
    ManifoldSheaf.manifoldFormSheafD E M n ≫ ManifoldSheaf.manifoldFormSheafD E M (n + 1) = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  exact ManifoldSheaf.manifoldFormPresheafD_squared E M n

variable {E M} {n : ℕ}

/-- Identifying global sections with global forms preserves exterior differentiation. -/
theorem Open.SmoothOpenManifoldForm.toGlobal_d (form : Open.SmoothOpenManifoldForm E (⊤ : Opens M) n) :
    Manifold.Algebra.SmoothManifoldForm.d (Open.SmoothOpenManifoldForm.toGlobal form) = Open.SmoothOpenManifoldForm.toGlobal (Open.SmoothOpenManifoldForm.d form) := by
  apply (Manifold.Algebra.SmoothManifoldForm.onTopEquiv (E := E) (M := M) (n := n + 1)).injective
  change Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Manifold.Algebra.SmoothManifoldForm.d (Open.SmoothOpenManifoldForm.toGlobal form)) =
    Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Open.SmoothOpenManifoldForm.toGlobal (Open.SmoothOpenManifoldForm.d form))
  rw [← Manifold.Algebra.SmoothManifoldForm.onOpen_d, Open.SmoothOpenManifoldForm.onOpen_toGlobal, Open.SmoothOpenManifoldForm.onOpen_toGlobal]

end

end OAI.Analysis.DifferentialForms.Manifold
