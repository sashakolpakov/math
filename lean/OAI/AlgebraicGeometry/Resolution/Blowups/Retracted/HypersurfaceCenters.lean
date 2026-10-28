import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation
import Mathlib.Algebra.Polynomial.Derivation

/-! # Hypersurface Centers -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.HypersurfaceCenters.Construction

noncomputable section

/-! Lifting hypersurface centers using the actual retraction and a normal derivation. -/

open _root_.Polynomial

variable {H V : Type*} [CommRing H] [CommRing V] [Algebra H V]

/-- When the hypersurface is identified with the base by an algebra
isomorphism, every center lifts by its base equations together with the normal coordinate. -/
theorem retracted_hypersurface_center_comap (z : V)
    (e : (V ⧸ Ideal.span {z}) ≃ₐ[H] H) (K : Ideal H) :
    K.map (algebraMap H V) ⊔ Ideal.span {z} =
      K.comap (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {z}))) := by
  let r := e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {z}))
  have hκ : r.comp (algebraMap H V) = RingHom.id H := by
    apply RingHom.ext
    intro h
    exact e.commutes h
  have hr : Function.Surjective r := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker r = Ideal.span {z} := by
    ext x
    change e (Ideal.Quotient.mk (Ideal.span {z}) x) = 0 ↔ x ∈ Ideal.span {z}
    rw [map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact e.injective
  have hmap : (K.map (algebraMap H V)).map r = K := by
    rw [Ideal.map_map, hκ, Ideal.map_id]
  have hc := Ideal.comap_map_of_surjective r hr (K.map (algebraMap H V))
  rw [hmap, ← RingHom.ker_eq_comap_bot, hker] at hc
  exact hc.symm

variable [Algebra H[X] V] [IsScalarTower H H[X] V] [Algebra.FormallyEtale H[X] V]

/-- The derivative in the normal coordinate, fixing every lifted hypersurface section. -/
def retractedHypersurfaceNormalDerivation : Derivation H V V :=
  Etale.Derivation.Construction.extendEtaleRingDerivation (S := V) (Polynomial.derivative' : Derivation H H[X] H[X])

theorem retractedHypersurfaceNormalDerivation_coordinate :
    retractedHypersurfaceNormalDerivation (H := H) (V := V) (algebraMap H[X] V X) = 1 := by
  rw [retractedHypersurfaceNormalDerivation, Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
  simp

theorem retractedHypersurfaceNormalDerivation_lifted_section (h : H) :
    retractedHypersurfaceNormalDerivation (H := H) (V := V) (algebraMap H V h) = 0 :=
  Derivation.map_algebraMap _ h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.HypersurfaceCenters.Construction
