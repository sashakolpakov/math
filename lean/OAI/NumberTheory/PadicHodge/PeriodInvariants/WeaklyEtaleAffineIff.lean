import OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleRingHom

/-! # Weakly Etale Affine Iff -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffineIff

noncomputable section

/-! # Weakly étale affine scheme maps and their ring maps -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable (R S : Type u) [CommRing R] [CommRing S]

theorem algebra [Algebra R S]
    (h : WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Algebra.WeaklyEtale R S where
  flat := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h.flat)
  flat_lmul' := by
    have hd := h.flat_diagonal
    rw [diagonal_SpecMap R S] at hd
    have : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' R (S := S)).toRingHom) ≫
        (pullbackSpecIso R S S).inv) := hd
    have hf := Flat.comp
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' R (S := S)).toRingHom) ≫
        (pullbackSpecIso R S S).inv) (pullbackSpecIso R S S).hom
    exact Flat.SpecMap_iff.mp (by simpa only [Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using hf)

theorem algebra_iff [Algebra R S] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
      Algebra.WeaklyEtale R S := by
  constructor
  · exact algebra R S
  · intro h
    have := h
    exact WeaklyEtaleAffine.specMap R S

theorem ringHom (f : R →+* S) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom f)) ↔
      WeaklyEtaleRingHom.Property f := by
  let : Algebra R S := f.toAlgebra
  exact algebra_iff R S

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WeaklyEtaleAffineIff
