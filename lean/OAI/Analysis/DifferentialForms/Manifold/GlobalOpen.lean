import OAI.Analysis.DifferentialForms.Manifold.OpenDeRhamX

/-! # Global Open -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
# Global forms and sections on the whole open domain

The two existing presentations of smooth forms agree: a global smooth
coefficient function is the same as a smooth section on the top open set.
The equivalence intertwines the actual exterior differentials and identifies
their de Rham complexes and cohomology groups.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped ContDiff

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

section

/-- A section on all of E is a global smooth form. -/
def OpenD.SmoothOpenForm.toGlobal : OpenD.SmoothOpenForm (⊤ : Opens E) n →ₗ[ℂ] Basic.SmoothForm E n where
  toFun form := ⟨form.extension, by
    change ContDiff ℝ ∞ form.extension
    apply contDiffOn_univ.mp
    simpa only [Opens.coe_top] using form.smooth⟩
  map_add' form otherForm := Subtype.ext (OpenD.SmoothOpenForm.extension_add form otherForm)
  map_smul' c form := Subtype.ext (OpenD.SmoothOpenForm.extension_smul c form)

@[simp] theorem OpenD.SmoothOpenForm.toGlobal_apply (form : OpenD.SmoothOpenForm (⊤ : Opens E) n) (x : E) :
    OpenD.SmoothOpenForm.toGlobal form x = form ⟨x, by simp⟩ := OpenD.SmoothOpenForm.extension_apply form ⟨x, by simp⟩

@[simp] theorem OpenD.SmoothOpenForm.onOpen_toGlobal (form : OpenD.SmoothOpenForm (⊤ : Opens E) n) :
    Basic.SmoothForm.onOpen ⊤ (OpenD.SmoothOpenForm.toGlobal form) = form := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  exact OpenD.SmoothOpenForm.extension_apply form x

/-- The inverse global-section map commutes with exterior differentiation. -/
theorem OpenD.SmoothOpenForm.toGlobal_d (form : OpenD.SmoothOpenForm (⊤ : Opens E) n) :
    Basic.SmoothForm.d (OpenD.SmoothOpenForm.toGlobal form) = OpenD.SmoothOpenForm.toGlobal (OpenD.SmoothOpenForm.d form) := by
  apply Basic.SmoothForm.ext
  intro x
  exact (OpenD.SmoothOpenForm.extension_apply (OpenD.SmoothOpenForm.d form) ⟨x, by simp⟩).symm

end

section

@[simp] theorem Basic.SmoothForm.toGlobal_onOpen (form : Basic.SmoothForm E n) :
    OpenD.SmoothOpenForm.toGlobal (Basic.SmoothForm.onOpen ⊤ form) = form := by
  apply Basic.SmoothForm.ext
  intro x
  exact OpenD.SmoothOpenForm.extension_apply (Basic.SmoothForm.onOpen ⊤ form) ⟨x, by simp⟩

/-- Global smooth forms are precisely smooth sections on the top open set. -/
def Basic.SmoothForm.onTopEquiv : Basic.SmoothForm E n ≃ₗ[ℂ] OpenD.SmoothOpenForm (⊤ : Opens E) n where
  toLinearMap := Basic.SmoothForm.onOpen ⊤
  invFun := OpenD.SmoothOpenForm.toGlobal
  left_inv := Basic.SmoothForm.toGlobal_onOpen
  right_inv := OpenD.SmoothOpenForm.onOpen_toGlobal

@[simp] theorem Basic.SmoothForm.onTopEquiv_apply (form : Basic.SmoothForm E n) :
    Basic.SmoothForm.onTopEquiv form = Basic.SmoothForm.onOpen ⊤ form := rfl

@[simp] theorem Basic.SmoothForm.onTopEquiv_symm_apply (form : OpenD.SmoothOpenForm (⊤ : Opens E) n) :
    Basic.SmoothForm.onTopEquiv.symm form = OpenD.SmoothOpenForm.toGlobal form := rfl

end

variable (E)

/-- The inverse of restricting the global de Rham complex to its whole domain. -/
def GlobalOpen.openTopDeRhamToGlobal : OpenDeRhamX.openDeRhamComplex (⊤ : Opens E) ⟶ DeRham.deRhamComplex E :=
  CochainComplex.ofHom (fun _ => ModuleCat.ofHom OpenD.SmoothOpenForm.toGlobal)
    (fun n => by
      rw [OpenDeRhamX.openDeRhamComplex_d, DeRham.deRhamComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro form
      exact OpenD.SmoothOpenForm.toGlobal_d form)

/-- Global and whole-domain de Rham complexes are canonically isomorphic. -/
def GlobalOpen.deRhamTopIso : DeRham.deRhamComplex E ≅ OpenDeRhamX.openDeRhamComplex (⊤ : Opens E) where
  hom := OpenDeRhamX.deRhamOnOpen ⊤
  inv := GlobalOpen.openTopDeRhamToGlobal E
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact Basic.SmoothForm.toGlobal_onOpen form
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact OpenD.SmoothOpenForm.onOpen_toGlobal form

/-- The induced identification of the two actual de Rham cohomology models. -/
def GlobalOpen.deRhamCohomologyTopIso (n : ℕ) :
    DeRham.deRhamCohomology E n ≅ OpenDeRhamX.openDeRhamCohomology (⊤ : Opens E) n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (GlobalOpen.deRhamTopIso E)

end

end OAI.Analysis.DifferentialForms.Manifold
