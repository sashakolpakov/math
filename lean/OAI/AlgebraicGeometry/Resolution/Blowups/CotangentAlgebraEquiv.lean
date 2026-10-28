import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Maps

/-! # Cotangent Algebra Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CotangentAlgebraEquiv.Construction

noncomputable section

/-! Actual ideal cotangent modules transport through algebra equivalences. -/

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

def idealCotangentAlgEquiv (e : R ≃ₐ[k] S) (I : Ideal R) (J : Ideal S) (h : I.map e.toRingHom = J) :
    I.Cotangent ≃ₗ[k] J.Cotangent := by
  have hf : I ≤ J.comap e.toRingHom := (Ideal.map_le_iff_le_comap).mp h.le
  have hg : J ≤ I.comap e.symm.toRingHom := by
    intro x hx
    have hm : e.symm x ∈ (I.map e.toRingHom).comap e.toRingHom := by
      change e (e.symm x) ∈ I.map e.toRingHom
      rwa [e.apply_symm_apply, h]
    rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hm
    exact hm
  refine {
    __ := Ideal.mapCotangent I J e.toAlgHom hf
    invFun := Ideal.mapCotangent J I e.symm.toAlgHom hg
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    change I.toCotangent ⟨e.symm (e x.val), hg (hf x.property)⟩ = I.toCotangent x
    apply congrArg I.toCotangent
    exact Subtype.ext (e.symm_apply_apply x.val)
  · intro x
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    change J.toCotangent ⟨e (e.symm x.val), hf (hg x.property)⟩ = J.toCotangent x
    apply congrArg J.toCotangent
    exact Subtype.ext (e.apply_symm_apply x.val)

theorem idealCotangentAlgEquiv_toCotangent (e : R ≃ₐ[k] S) (I : Ideal R) (J : Ideal S)
    (h : I.map e.toRingHom = J) (x : I) :
    idealCotangentAlgEquiv e I J h (I.toCotangent x) =
      J.toCotangent ⟨e x.val, h ▸ Ideal.mem_map_of_mem e.toRingHom x.property⟩ := rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CotangentAlgebraEquiv.Construction
