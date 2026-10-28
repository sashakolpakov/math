import OAI.Analysis.DifferentialForms.Manifold.ClosedPullback
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # De Rham Diffeomorph -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

/-!
Invariance of the actual manifold de Rham complex under smooth diffeomorphisms.
Every forward map is pullback by the supplied diffeomorphism, and every inverse
is pullback by its genuine inverse. Their inverse laws are proved below.
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

/-- A smooth diffeomorphism acts by a complex-linear equivalence on actual forms. -/
def Algebra.SmoothManifoldForm.diffeomorphPullback
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    Algebra.SmoothManifoldForm F N n ≃ₗ[ℂ] Algebra.SmoothManifoldForm E M n where
  toLinearMap := Algebra.SmoothManifoldForm.pullback e e.contMDiff
  invFun := Algebra.SmoothManifoldForm.pullback e.symm e.symm.contMDiff
  left_inv form := by
    change Algebra.SmoothManifoldForm.pullback e.symm e.symm.contMDiff
      (Algebra.SmoothManifoldForm.pullback e e.contMDiff form) = form
    rw [← Algebra.SmoothManifoldForm.pullback_comp e.symm e.symm.contMDiff e e.contMDiff]
    have he : (e : M → N) ∘ (e.symm : N → M) = id := funext e.apply_symm_apply
    simpa only [he] using Algebra.SmoothManifoldForm.pullback_id form
  right_inv form := by
    change Algebra.SmoothManifoldForm.pullback e e.contMDiff
      (Algebra.SmoothManifoldForm.pullback e.symm e.symm.contMDiff form) = form
    rw [← Algebra.SmoothManifoldForm.pullback_comp e e.contMDiff e.symm e.symm.contMDiff]
    have he : (e.symm : N → M) ∘ (e : M → N) = id := funext e.symm_apply_apply
    simpa only [he] using Algebra.SmoothManifoldForm.pullback_id form

@[simp]
theorem Algebra.SmoothManifoldForm.diffeomorphPullback_apply
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) (form : Algebra.SmoothManifoldForm F N n) :
    Algebra.SmoothManifoldForm.diffeomorphPullback e n form = Algebra.SmoothManifoldForm.pullback e e.contMDiff form := rfl

@[simp]
theorem Algebra.SmoothManifoldForm.diffeomorphPullback_symm_apply
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) (form : Algebra.SmoothManifoldForm E M n) :
    (Algebra.SmoothManifoldForm.diffeomorphPullback e n).symm form = Algebra.SmoothManifoldForm.pullback e.symm e.symm.contMDiff form := rfl

theorem Algebra.SmoothManifoldForm.d_diffeomorphPullback
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) (form : Algebra.SmoothManifoldForm F N n) :
    Algebra.SmoothManifoldForm.d (Algebra.SmoothManifoldForm.diffeomorphPullback e n form) = Algebra.SmoothManifoldForm.diffeomorphPullback e (n + 1) (Algebra.SmoothManifoldForm.d form) :=
  Algebra.SmoothManifoldForm.d_pullback e e.contMDiff form

/-- The actual de Rham complexes are isomorphic by diffeomorphism pullback. -/
def DeRhamDiffeomorph.manifoldDeRhamDiffeomorph (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    ManifoldDeRham.manifoldDeRhamComplex F N ≅ ManifoldDeRham.manifoldDeRhamComplex E M where
  hom := ManifoldDeRhamPullback.manifoldDeRhamPullback e e.contMDiff
  inv := ManifoldDeRhamPullback.manifoldDeRhamPullback e.symm e.symm.contMDiff
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact (Algebra.SmoothManifoldForm.diffeomorphPullback e n).symm_apply_apply form
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro form
    exact (Algebra.SmoothManifoldForm.diffeomorphPullback e n).apply_symm_apply form

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamDiffeomorph_hom (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    (DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e).hom = ManifoldDeRhamPullback.manifoldDeRhamPullback e e.contMDiff := rfl

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamDiffeomorph_inv (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    (DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e).inv = ManifoldDeRhamPullback.manifoldDeRhamPullback e.symm e.symm.contMDiff := rfl

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamDiffeomorph_refl :
    DeRhamDiffeomorph.manifoldDeRhamDiffeomorph (Diffeomorph.refl 𝓘(ℝ, E) M ∞) =
      Iso.refl (ManifoldDeRham.manifoldDeRhamComplex E M) := by
  apply Iso.ext
  exact ManifoldDeRhamPullback.manifoldDeRhamPullback_id

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamDiffeomorph_symm (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) :
    DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e.symm = (DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e).symm := by
  apply Iso.ext
  rfl

theorem DeRhamDiffeomorph.manifoldDeRhamDiffeomorph_trans
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (f : N ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ P) :
    DeRhamDiffeomorph.manifoldDeRhamDiffeomorph (e.trans f) =
      DeRhamDiffeomorph.manifoldDeRhamDiffeomorph f ≪≫ DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e := by
  apply Iso.ext
  exact ManifoldDeRhamPullback.manifoldDeRhamPullback_comp e e.contMDiff f f.contMDiff

/-- Diffeomorphism invariance of genuine complex de Rham cohomology. -/
def DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    ManifoldDeRham.manifoldDeRhamCohomology F N n ≅ ManifoldDeRham.manifoldDeRhamCohomology E M n :=
  HomologicalComplex.homologyMapIso (DeRhamDiffeomorph.manifoldDeRhamDiffeomorph e) n

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_hom
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    (DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e n).hom =
      ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback e e.contMDiff n := rfl

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_inv
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    (DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e n).inv =
      ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback e.symm e.symm.contMDiff n := rfl

/-- Diffeomorphism pullback restricts to an equivalence on actual closed forms. -/
def DeRhamDiffeomorph.manifoldClosedFormsDiffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    ManifoldDeRham.manifoldClosedForms F N n ≃ₗ[ℂ] ManifoldDeRham.manifoldClosedForms E M n where
  toLinearMap := ClosedPullback.manifoldClosedFormsPullback e e.contMDiff n
  invFun := ClosedPullback.manifoldClosedFormsPullback e.symm e.symm.contMDiff n
  left_inv form := by
    apply Subtype.ext
    exact (Algebra.SmoothManifoldForm.diffeomorphPullback e n).symm_apply_apply form.val
  right_inv form := by
    apply Subtype.ext
    exact (Algebra.SmoothManifoldForm.diffeomorphPullback e n).apply_symm_apply form.val

/-- The cohomology isomorphism sends a closed-form class to the class of its
actual pullback, with no chosen representative or comparison data. -/
theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_class
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) (form : ManifoldDeRham.manifoldClosedForms F N n) :
    (DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e n).hom (ManifoldDeRham.manifoldDeRhamFormClass F N n form) =
      ManifoldDeRham.manifoldDeRhamFormClass E M n (DeRhamDiffeomorph.manifoldClosedFormsDiffeomorph e n form) :=
  ClosedPullback.manifoldDeRhamFormClass_pullback_apply e e.contMDiff n form

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_refl (n : ℕ) :
    DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph (Diffeomorph.refl 𝓘(ℝ, E) M ∞) n =
      Iso.refl (ManifoldDeRham.manifoldDeRhamCohomology E M n) := by
  apply Iso.ext
  exact ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback_id n

@[simp]
theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_symm
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (n : ℕ) :
    DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e.symm n =
      (DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e n).symm := by
  apply Iso.ext
  rfl

theorem DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph_trans
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ N) (f : N ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, G)⟯ P) (n : ℕ) :
    DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph (e.trans f) n =
      DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph f n ≪≫ DeRhamDiffeomorph.manifoldDeRhamCohomologyDiffeomorph e n := by
  apply Iso.ext
  exact ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback_comp e e.contMDiff f f.contMDiff n

end

end OAI.Analysis.DifferentialForms.Manifold
