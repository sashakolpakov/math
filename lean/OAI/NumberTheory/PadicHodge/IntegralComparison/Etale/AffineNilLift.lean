import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.NilLifting
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Affine Nil Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineNilLift

noncomputable section

/-! Unique lifting of an actual affine-scheme map into a native etale
chart through any surjective nilpotent ring reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra.Etale R A]
  (ρ : B →+* C) (hρ : Function.Surjective ρ)
  (hnil : ∀ x ∈ RingHom.ker ρ, IsNilpotent x)
  (z : Spec (.of B) ⟶ Spec (.of R)) (a : Spec (.of C) ⟶ Spec (.of A))
  (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
    Spec.map (CommRingCat.ofHom ρ) ≫ z)

include hρ hnil ha in
theorem existsUnique_lift : ∃! l : Spec (.of B) ⟶ Spec (.of A),
    Spec.map (CommRingCat.ofHom ρ) ≫ l = a ∧
      l ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) = z := by
  let : Algebra R B := (Spec.preimage z).hom.toAlgebra
  let : Algebra R C := (ρ.comp (Spec.preimage z).hom).toAlgebra
  let π : B →ₐ[R] C := { ρ with commutes' := fun _ => rfl }
  let u : A →ₐ[R] C := { (Spec.preimage a).hom with
    commutes' := fun r => by
      have h := congrArg Spec.preimage ha
      simp only [Spec.preimage_comp, Spec.preimage_map] at h
      exact ConcreteCategory.congr_hom h r }
  obtain ⟨v, hv, huniq⟩ := NilLifting.existsUnique_lift u π hρ hnil
  refine ⟨Spec.map (CommRingCat.ofHom v.toRingHom), ⟨?_, ?_⟩, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_preimage a]
    exact congrArg (fun f : A →ₐ[R] C => Spec.map (CommRingCat.ofHom f.toRingHom)) hv
  · rw [← Spec.map_comp, ← Spec.map_preimage z]
    apply congrArg (fun f : R →+* B => Spec.map (CommRingCat.ofHom f))
    exact v.comp_algebraMap
  · intro l hl
    let w : A →ₐ[R] B := { (Spec.preimage l).hom with
      commutes' := fun r => by
        have h := congrArg Spec.preimage hl.2
        simp only [Spec.preimage_comp, Spec.preimage_map] at h
        exact ConcreteCategory.congr_hom h r }
    have hw : π.comp w = u := by
      ext x
      have h := congrArg Spec.preimage hl.1
      simp only [Spec.preimage_comp, Spec.preimage_map] at h
      exact ConcreteCategory.congr_hom h x
    have he := huniq w hw
    rw [← Spec.map_preimage l]
    exact congrArg (fun f : A →ₐ[R] B => Spec.map (CommRingCat.ofHom f.toRingHom)) he

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.AffineNilLift
