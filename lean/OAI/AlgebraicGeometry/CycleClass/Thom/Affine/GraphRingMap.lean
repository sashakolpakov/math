import Mathlib.RingTheory.TensorProduct.Maps

/-! # Graph Ring Map -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap.Constructions

noncomputable section

/-! The actual tensor-product coordinate-ring map defining an affine graph is surjective whenever its coordinate presentation is. -/

open scoped TensorProduct

variable {k R S A : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing A]
  [Algebra k R] [Algebra k S] [Algebra k A]

def graphRingMap (h : R →ₐ[k] A) (f : S →ₐ[k] A) : R ⊗[k] S →ₐ[k] A :=
  Algebra.TensorProduct.lift h f (fun _ _ => Commute.all _ _)

theorem graphRingMap_left (h : R →ₐ[k] A) (f : S →ₐ[k] A) :
    (graphRingMap h f).comp Algebra.TensorProduct.includeLeft = h :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

theorem graphRingMap_right (h : R →ₐ[k] A) (f : S →ₐ[k] A) :
    (graphRingMap h f).comp Algebra.TensorProduct.includeRight = f :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

theorem graphRingMap_surjective (h : R →ₐ[k] A) (f : S →ₐ[k] A) (hf : Function.Surjective f) :
    Function.Surjective (graphRingMap h f) := by
  intro a
  obtain ⟨s, rfl⟩ := hf a
  exact ⟨Algebra.TensorProduct.includeRight s, AlgHom.congr_fun (graphRingMap_right h f) s⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.GraphRingMap.Constructions
