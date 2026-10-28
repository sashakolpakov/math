import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Ring Pushout Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPushoutTensorComparison

noncomputable section

/-! The canonical tensor map for a pushout of commutative rings is bijective. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

theorem tensorLift_bijective_of_isPushout (i : A →ₐ[R] C) (j : B →ₐ[R] C)
    (H : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom i.toRingHom) (CommRingCat.ofHom j.toRingHom)) :
    Function.Bijective (Algebra.TensorProduct.lift i j (fun _ _ => .all _ _)) := by
  let H₀ := CommRingCat.isPushout_tensorProduct R A B
  let e := H₀.isoIsPushout (CommRingCat.of A) (CommRingCat.of B) H
  have he : CommRingCat.ofHom
      (Algebra.TensorProduct.lift i j (fun _ _ => .all _ _)).toRingHom = e.hom := by
    apply H₀.hom_ext
    · change _ = _ ≫ (H₀.isoIsPushout (CommRingCat.of A) (CommRingCat.of B) H).hom
      rw [IsPushout.inl_isoIsPushout_hom]
      ext a
      simp
    · change _ = _ ≫ (H₀.isoIsPushout (CommRingCat.of A) (CommRingCat.of B) H).hom
      rw [IsPushout.inr_isoIsPushout_hom]
      ext b
      simp
  have hfun : (Algebra.TensorProduct.lift i j (fun _ _ => .all _ _)) =
      e.commRingCatIsoToRingEquiv.toRingHom := by
    exact congrArg CommRingCat.Hom.hom he
  exact (congrArg (fun k : (TensorProduct R A B) →+* C => Function.Bijective k) hfun).mpr
    e.commRingCatIsoToRingEquiv.bijective

theorem isPushout_of_tensorLift_bijective (i : A →ₐ[R] C) (j : B →ₐ[R] C)
    (h : Function.Bijective (Algebra.TensorProduct.lift i j (fun _ _ => .all _ _))) :
    IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom i.toRingHom) (CommRingCat.ofHom j.toRingHom) := by
  let l := CommRingCat.ofHom (Algebra.TensorProduct.lift i j
    (fun _ _ => .all _ _)).toRingHom
  have : IsIso l := (ConcreteCategory.isIso_iff_bijective l).mpr h
  refine (CommRingCat.isPushout_tensorProduct R A B).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso l) ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext r
    simp [l]
  · ext r
    simp [l]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPushoutTensorComparison
