import OAI.AlgebraicGeometry.HilbertScheme.Presentations.TensorCokernelInjectivity
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Boundary -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Boundary

noncomputable section

/-! The actual connecting map from an ideal-tensor obstruction to the
kernel of a quotient presentation, with its elementwise formula. -/

open TensorProduct

universe u v w t
variable {B : Type u} [CommRing B]
variable {K : Type v} [AddCommGroup K] [Module B K]
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {M : Type t} [AddCommGroup M] [Module B M]
variable (f : K →ₗ[B] F) (g : F →ₗ[B] M)
variable (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g)
variable (I : Ideal B)

def idealTensorBoundary : (I.subtype.lTensor M).ker →ₗ[B] K ⊗[B] (B ⧸ I) :=
  SnakeLemma.δ' (I.subtype.lTensor K) (I.subtype.lTensor F) (I.subtype.lTensor M)
    (f.rTensor I) (g.rTensor I) (rTensor_exact I hex hg)
    (f.rTensor B) (g.rTensor B) (rTensor_exact B hex hg)
    (by simp only [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])
    (by simp only [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])
    (I.subtype.lTensor M).ker.subtype (I.subtype.lTensor M).exact_subtype_ker_map
    (I.mkQ.lTensor K) (lTensor_exact K (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)
    (LinearMap.rTensor_surjective I hg)
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

theorem idealTensorBoundary_eq (x : (I.subtype.lTensor M).ker)
    (y : F ⊗[B] I) (hy : g.rTensor I y = x.val)
    (z : K ⊗[B] B) (hz : f.rTensor B z = I.subtype.lTensor F y) :
    idealTensorBoundary f g hf hex hg I x = I.mkQ.lTensor K z := by
  exact SnakeLemma.δ'_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x y hy z hz

theorem idealTensorBoundary_exact :
    Function.Exact (idealTensorBoundary f g hf hex hg I) (f.rTensor (B ⧸ I)) := by
  apply SnakeLemma.exact_δ'_left
    (I.subtype.lTensor K) (I.subtype.lTensor F) (I.subtype.lTensor M)
    (f.rTensor I) (g.rTensor I) (rTensor_exact I hex hg)
    (f.rTensor B) (g.rTensor B) (rTensor_exact B hex hg)
    (by simp only [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])
    (by simp only [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])
    (I.subtype.lTensor M).ker.subtype (I.subtype.lTensor M).exact_subtype_ker_map
    (I.mkQ.lTensor K) (lTensor_exact K (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)
    (I.mkQ.lTensor F) (lTensor_exact F (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)
    (LinearMap.rTensor_surjective I hg)
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)
    (f.rTensor (B ⧸ I))
    (by simp only [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])
    (LinearMap.lTensor_surjective K I.mkQ_surjective)

theorem idealTensorBoundary_injective [Module.Flat B F] :
    Function.Injective (idealTensorBoundary f g hf hex hg I) := by
  let vF := I.subtype.lTensor F
  let vM := I.subtype.lTensor M
  let d : vF.ker →ₗ[B] vM.ker :=
    ((g.rTensor I).comp vF.ker.subtype).codRestrict vM.ker (fun x => by
      change I.subtype.lTensor M (g.rTensor I x.val) = 0
      rw [← TensorInjectivityExtensions.tensorMap_exchange, x.property, map_zero])
  have hd : Function.Exact d (idealTensorBoundary f g hf hex hg I) := by
    apply SnakeLemma.exact_δ'_right
      (I.subtype.lTensor K) vF vM
      (f.rTensor I) (g.rTensor I) (rTensor_exact I hex hg)
      (f.rTensor B) (g.rTensor B) (rTensor_exact B hex hg)
      (by ext x r; rfl)
      (by ext x r; rfl)
      vF.ker.subtype vF.exact_subtype_ker_map
      vM.ker.subtype vM.exact_subtype_ker_map
      (I.mkQ.lTensor K) (lTensor_exact K (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)
      (LinearMap.rTensor_surjective I hg)
      (Module.Flat.rTensor_preserves_injective_linearMap f hf)
      d rfl vM.ker.subtype_injective
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, rfl⟩ := (hd x).mp hx
  have hy : y = 0 := by
    apply Subtype.ext
    exact (Module.Flat.lTensor_preserves_injective_linearMap (M := F)
      I.subtype I.subtype_injective) (y.property.trans (map_zero _).symm)
  rw [hy, map_zero]

def idealTensorBoundaryEquiv [Module.Flat B F] :
    (I.subtype.lTensor M).ker ≃ₗ[B] (f.rTensor (B ⧸ I)).ker :=
  LinearEquiv.ofBijective
    ((idealTensorBoundary f g hf hex hg I).codRestrict _
      (fun x => (idealTensorBoundary_exact f g hf hex hg I).apply_apply_eq_zero x))
    ⟨fun x y hxy => idealTensorBoundary_injective f g hf hex hg I (congrArg Subtype.val hxy),
      fun y => by
        obtain ⟨x, hx⟩ := (idealTensorBoundary_exact f g hf hex hg I y.val).mp y.property
        exact ⟨x, Subtype.ext hx⟩⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Boundary
