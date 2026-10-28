import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FrobeniusAlgebra

/-! # Geometric Fiber -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GeometricFiber

noncomputable section

/-! The original geometric fiber of an affine scheme is its actual affine tensor-product fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable (k A : Type u) [Field k] [CommRing A] [Algebra k A]

local notation "Ω" => AlgebraicClosure k
local notation "T" => Ω ⊗[k] A
local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))

def iso : Frobenius.Geometry.geometricFiber (L := Ω) f ≅ Spec (CommRingCat.of T) :=
  pullbackSymmetry f b ≪≫ pullbackSpecIso k Ω A

theorem inv_fst : (iso k A).inv ≫ pullback.fst f b =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : A →ₐ[k] T).toRingHom) := by
  simp only [iso, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSpecIso_inv_snd]
  rfl

theorem inv_snd : (iso k A).inv ≫ pullback.snd f b =
    Spec.map (CommRingCat.ofHom (algebraMap Ω T)) := by
  simp only [iso, Iso.trans_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, pullbackSpecIso_inv_fst']

theorem scalar_natural (σ : Ω ≃ₐ[k] Ω) :
    (iso k A).inv ≫ (Frobenius.Geometry.geometricFiberIso f σ).hom =
      Spec.map (CommRingCat.ofHom (FiniteEtale.FrobeniusAlgebra.scalarMap k A σ).toRingHom) ≫ (iso k A).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, Frobenius.Geometry.geometricFiberIso_hom_fst, Category.assoc, inv_fst,
      ← Spec.map_comp]
    congr 1
    ext x
    change (1 : Ω) ⊗ₜ[k] x = σ 1 ⊗ₜ[k] x
    rw [map_one]
  · rw [Category.assoc, Frobenius.Geometry.geometricFiberIso_hom_snd, ← Category.assoc, inv_snd,
      Category.assoc, inv_snd]
    change Spec.map (CommRingCat.ofHom (algebraMap Ω T)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) = _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GeometricFiber
