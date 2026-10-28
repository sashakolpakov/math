import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RingPushoutTensorComparison
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Surjective Ring Pushout Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveRingPushoutQuotient

noncomputable section

/-! Pushing out a surjective ring map gives the quotient by its extended
kernel. The comparison preserves any compatible coefficient action. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u
variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]

def pushoutQuotientEquivOfSurjective
    (f : R →+* B) (g : R →+* C) (u : B →+* D) (v : C →+* D)
    (H : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom u) (CommRingCat.ofHom v)) (hg : Function.Surjective g) :
    (B ⧸ (RingHom.ker g).map f) ≃+* D := by
  let I := RingHom.ker g
  let J := I.map f
  let κ := Ideal.Quotient.mk J
  have hκ : I ≤ RingHom.ker (κ.comp f) := by
    intro r hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f hr)
  let lC : R ⧸ I →+* B ⧸ J := Ideal.Quotient.lift I (κ.comp f) hκ
  let eC := g.quotientKerEquivOfSurjective hg
  let v₀ : C →+* B ⧸ J := lC.comp eC.symm.toRingHom
  have hv₀ (r : R) : v₀ (g r) = κ (f r) := by
    change lC (eC.symm (g r)) = κ (f r)
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
    rfl
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom κ =
      CommRingCat.ofHom g ≫ CommRingCat.ofHom v₀ := by
    ext r
    exact (hv₀ r).symm
  have hu : J ≤ RingHom.ker u := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change u (f r) = 0
    have h := ConcreteCategory.congr_hom H.w r
    change u (f r) = v (g r) at h
    exact h.trans (by rw [show g r = 0 from hr, map_zero])
  let l : B ⧸ J →+* D := Ideal.Quotient.lift J u hu
  let m := (H.desc (CommRingCat.ofHom κ) (CommRingCat.ofHom v₀) hcomm).hom
  have hm (b : B) : m (u b) = κ b :=
    ConcreteCategory.congr_hom (H.inl_desc (CommRingCat.ofHom κ) (CommRingCat.ofHom v₀) hcomm) b
  have hn (c : C) : m (v c) = v₀ c :=
    ConcreteCategory.congr_hom (H.inr_desc (CommRingCat.ofHom κ) (CommRingCat.ofHom v₀) hcomm) c
  have hright : CommRingCat.ofHom m ≫ CommRingCat.ofHom l = 𝟙 (CommRingCat.of D) := by
    apply H.hom_ext
    · ext b
      change l (m (u b)) = u b
      rw [hm]
      rfl
    · ext c
      obtain ⟨r, rfl⟩ := hg c
      change l (m (v (g r))) = v (g r)
      rw [hn, hv₀]
      exact ConcreteCategory.congr_hom H.w r
  exact {
    l with
    invFun := m
    left_inv := by
      intro x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact hm b
    right_inv := fun d => ConcreteCategory.congr_hom hright d }

theorem pushoutQuotientEquivOfSurjective_mk
    (f : R →+* B) (g : R →+* C) (u : B →+* D) (v : C →+* D)
    (H : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom u) (CommRingCat.ofHom v)) (hg : Function.Surjective g) (b : B) :
    pushoutQuotientEquivOfSurjective f g u v H hg (Ideal.Quotient.mk _ b) = u b := rfl

def pushoutQuotientAlgEquivOfSurjective
    {K : Type u} [CommRing K] [Algebra K B] [Algebra K D]
    (f : R →+* B) (g : R →+* C) (u : B →+* D) (v : C →+* D)
    (H : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom u) (CommRingCat.ofHom v)) (hg : Function.Surjective g)
    (hu : ∀ k : K, u (algebraMap K B k) = algebraMap K D k) :
    (B ⧸ (RingHom.ker g).map f) ≃ₐ[K] D :=
  { pushoutQuotientEquivOfSurjective f g u v H hg with
    commutes' k := hu k }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveRingPushoutQuotient
