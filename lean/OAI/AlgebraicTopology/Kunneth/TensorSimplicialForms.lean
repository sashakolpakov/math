import OAI.AlgebraicTopology.Kunneth.SimplicialForms
import OAI.AlgebraicTopology.Kunneth.CochainModelHomotopy
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor Simplicial Forms -/

namespace OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms

noncomputable section

/-! The exact simplicial model for comparison with a fixed closed right factor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite
open scoped Simplicial TensorProduct

namespace Constructions

abbrev SimplexFormTensor (q n p : ℕ) :=
  RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p ⊗[ℂ] ↥(SimplicialForms.Constructions.SimplexClosedForms n q)

def simplexFormTensorPullback {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (q p : ℕ) : SimplexFormTensor q n p →ₗ[ℂ] SimplexFormTensor q m p :=
  TensorProduct.map (SimplexFormMaps.Constructions.simplexFormPullback f p) (SimplicialForms.Constructions.simplexClosedFormPullback f q)

theorem simplexFormTensorPullback_id (n q p : ℕ) :
    simplexFormTensorPullback (id : Fin (n + 1) → Fin (n + 1)) q p = LinearMap.id := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change SimplexFormMaps.Constructions.simplexFormPullback (id : Fin (n + 1) → Fin (n + 1)) p a ⊗ₜ[ℂ]
    SimplicialForms.Constructions.simplexClosedFormPullback (id : Fin (n + 1) → Fin (n + 1)) q b = a ⊗ₜ b
  rw [SimplexFormMaps.Constructions.simplexFormPullback_id]
  congr 1
  apply Subtype.ext
  exact SimplexFormMaps.Constructions.simplexFormPullback_id n q b.val

theorem simplexFormTensorPullback_comp {l m n : ℕ}
    (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (n + 1)) (q p : ℕ) :
    simplexFormTensorPullback (g ∘ f) q p =
      (simplexFormTensorPullback f q p).comp (simplexFormTensorPullback g q p) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change SimplexFormMaps.Constructions.simplexFormPullback (g ∘ f) p a ⊗ₜ[ℂ] SimplicialForms.Constructions.simplexClosedFormPullback (g ∘ f) q b =
    SimplexFormMaps.Constructions.simplexFormPullback f p (SimplexFormMaps.Constructions.simplexFormPullback g p a) ⊗ₜ[ℂ]
      SimplicialForms.Constructions.simplexClosedFormPullback f q (SimplicialForms.Constructions.simplexClosedFormPullback g q b)
  rw [SimplexFormMaps.Constructions.simplexFormPullback_comp f g]
  congr 1
  apply Subtype.ext
  exact SimplexFormMaps.Constructions.simplexFormPullback_comp f g q b.val

def simplexFormsTensor (q p : ℕ) : SimplicialObject (ModuleCat ℂ) where
  obj n := ModuleCat.of ℂ (SimplexFormTensor q n.unop.len p)
  map θ := ModuleCat.ofHom (simplexFormTensorPullback θ.unop q p)
  map_id n := ModuleCat.hom_ext (simplexFormTensorPullback_id n.unop.len q p)
  map_comp θ φ := ModuleCat.hom_ext (simplexFormTensorPullback_comp φ.unop θ.unop q p)

def simplexFormTensorD (q n p : ℕ) :
    SimplexFormTensor q n p →ₗ[ℂ] SimplexFormTensor q n (p + 1) :=
  (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p).rTensor
    ↥(SimplicialForms.Constructions.SimplexClosedForms n q)

@[simp] theorem simplexFormTensorD_tmul (q n p : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) (b : SimplicialForms.Constructions.SimplexClosedForms n q) :
    simplexFormTensorD q n p (a ⊗ₜ[ℂ] b) =
      RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p a ⊗ₜ[ℂ] b := rfl

def simplexFormsTensorDifferential (q p : ℕ) :
    simplexFormsTensor q p ⟶ simplexFormsTensor q (p + 1) where
  app n := ModuleCat.ofHom (simplexFormTensorD q n.unop.len p)
  naturality {n m} θ := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn m.unop.len) p
        (SimplexFormMaps.Constructions.simplexFormPullback θ.unop p a) ⊗ₜ[ℂ] SimplicialForms.Constructions.simplexClosedFormPullback θ.unop q b =
      SimplexFormMaps.Constructions.simplexFormPullback θ.unop (p + 1)
        (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n.unop.len) p a) ⊗ₜ[ℂ]
          SimplicialForms.Constructions.simplexClosedFormPullback θ.unop q b
    rw [SimplexFormMaps.Constructions.simplexFormPullback_d]

theorem simplexFormTensorD_exact (q n p : ℕ)
    (a : SimplexFormTensor q n (p + 1)) (ha : simplexFormTensorD q n (p + 1) a = 0) :
    ∃ b : SimplexFormTensor q n p, simplexFormTensorD q n p b = a := by
  have he : Function.Exact
      (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p)
      (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) (p + 1)) := by
    intro x
    constructor
    · exact RestrictedForms.Constructions.restrictedFormD_exact (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n)
        (SimplexFormDomain.Constructions.coordinateSimplex_starConvex n) p x
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (RestrictedForms.Constructions.restrictedFormD_squared (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p) y
  exact (Module.Flat.rTensor_exact ↥(SimplicialForms.Constructions.SimplexClosedForms n q) he a).mp ha

def simplexFormTensorBoundary (q n p : ℕ) :
    SimplexFormTensor q (n + 1) p →ₗ[ℂ] SimplexFormTensor q n p :=
  (AlgebraicTopology.AlternatingFaceMapComplex.objD (simplexFormsTensor q p) n).hom

def simplexFormTensorDelta (q n p : ℕ) :
    (SimplexFormTensor q n p →ₗ[ℂ] ℂ) →ₗ[ℂ]
      (SimplexFormTensor q (n + 1) p →ₗ[ℂ] ℂ) :=
  (simplexFormTensorBoundary q n p).dualMap

theorem simplexFormTensorBoundary_apply (q n p : ℕ) (a : SimplexFormTensor q (n + 1) p) :
    simplexFormTensorBoundary q n p a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        simplexFormTensorPullback (SimplexCategory.δ j) q p a := by
  simp only [simplexFormTensorBoundary, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    simplexFormTensorPullback (SimplexCategory.δ j) q p) a = _
  rw [LinearMap.sum_apply]
  rfl

theorem simplexFormTensorDelta_apply (q n p : ℕ)
    (H : SimplexFormTensor q n p →ₗ[ℂ] ℂ) (a : SimplexFormTensor q (n + 1) p) :
    simplexFormTensorDelta q n p H a =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
        H (simplexFormTensorPullback (SimplexCategory.δ j) q p a) := by
  change H (simplexFormTensorBoundary q n p a) = _
  rw [simplexFormTensorBoundary_apply, map_sum]
  simp only [map_zsmul]

theorem simplexFormTensorBoundary_squared (q n p : ℕ) :
    (simplexFormTensorBoundary q n p).comp (simplexFormTensorBoundary q (n + 1) p) = 0 :=
  congrArg ModuleCat.Hom.hom
    (AlgebraicTopology.AlternatingFaceMapComplex.d_squared (simplexFormsTensor q p) n)

theorem simplexFormTensorBoundary_d (q n p : ℕ) :
    (simplexFormTensorD q n p).comp (simplexFormTensorBoundary q n p) =
      (simplexFormTensorBoundary q n (p + 1)).comp (simplexFormTensorD q (n + 1) p) := by
  let f := AlgebraicTopology.AlternatingFaceMapComplex.map
    (simplexFormsTensorDifferential q p)
  have h := congrArg ModuleCat.Hom.hom (f.comm (n + 1) n)
  simpa only [f, AlgebraicTopology.AlternatingFaceMapComplex.map_f,
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq,
    simplexFormTensorBoundary, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    simplexFormsTensorDifferential, ModuleCat.hom_comp, ModuleCat.hom_ofHom] using h.symm

theorem simplexFormTensorDelta_d (q n p : ℕ)
    (H : SimplexFormTensor q n (p + 1) →ₗ[ℂ] ℂ) :
    simplexFormTensorDelta q n p (H.comp (simplexFormTensorD q n p)) =
      (simplexFormTensorDelta q n (p + 1) H).comp (simplexFormTensorD q (n + 1) p) := by
  apply LinearMap.ext
  intro a
  exact congrArg H (LinearMap.congr_fun (simplexFormTensorBoundary_d q n p) a)

theorem simplexFormTensorDelta_squared (q n p : ℕ)
    (H : SimplexFormTensor q n p →ₗ[ℂ] ℂ) :
    simplexFormTensorDelta q (n + 1) p (simplexFormTensorDelta q n p H) = 0 := by
  apply LinearMap.ext
  intro a
  change H (simplexFormTensorBoundary q n p (simplexFormTensorBoundary q (n + 1) p a)) = 0
  rw [show simplexFormTensorBoundary q n p (simplexFormTensorBoundary q (n + 1) p a) = 0
    from LinearMap.congr_fun (simplexFormTensorBoundary_squared q n p) a, map_zero]

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.TensorSimplicialForms
