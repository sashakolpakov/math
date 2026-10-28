import OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationIdeal

/-! # Augmentation Coefficient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationCoefficient.AugmentationCoefficientQuotient

noncomputable section

/-!
# Augmented PD algebras modulo coefficient ideals

An arbitrary coefficient quotient of an augmented PD algebra inherits
divided powers. Its augmentation maps to the quotient coefficient ring,
and the descended PD ideal is exactly the kernel of that augmentation.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (L : Ideal R)

def Ring := A ⧸ L.map (algebraMap R A)

instance ringCommRing : CommRing (Ring R A L) :=
  inferInstanceAs (CommRing (A ⧸ L.map (algebraMap R A)))

instance ringAlgebra : Algebra R (Ring R A L) :=
  inferInstanceAs (Algebra R (A ⧸ L.map (algebraMap R A)))

def quotient : A →ₐ[R] Ring R A L := Ideal.Quotient.mkₐ R (L.map (algebraMap R A))

def constants : (R ⧸ L) →ₐ[R] Ring R A L :=
  Ideal.Quotient.liftₐ L (Algebra.ofId R (Ring R A L)) (fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

theorem constants_mk (a : R) :
    constants R A L (Ideal.Quotient.mk L a) = quotient R A L (algebraMap R A a) := rfl

variable (ε : A →ₐ[R] R)

def ideal : Ideal (Ring R A L) := (RingHom.ker ε.toRingHom).map (quotient R A L).toRingHom

def reduction : Ring R A L →ₐ[R] (R ⧸ L) :=
  Ideal.Quotient.liftₐ (L.map (algebraMap R A)) ((Ideal.Quotient.mkₐ R L).comp ε) (by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have h := Base.IdealQuotient.BaseIdealQuotient.map_mem L ε.toLinearMap ha
    rw [Algebra.algebraMap_self, Ideal.map_id] at h
    exact h)

theorem reduction_quotient (a : A) :
    reduction R A L ε (quotient R A L a) = Ideal.Quotient.mk L (ε a) := rfl

theorem reduction_constants :
    (reduction R A L ε).comp (constants R A L) = AlgHom.id R (R ⧸ L) := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [AlgHom.comp_apply, constants_mk, reduction_quotient, ε.commutes]
  rfl

include ε in
theorem constants_injective : Function.Injective (constants R A L) := by
  intro a b hab
  have he := congrArg (reduction R A L ε) hab
  have hleft := AlgHom.congr_fun (reduction_constants R A L ε) a
  have hright := AlgHom.congr_fun (reduction_constants R A L ε) b
  exact hleft.symm.trans (he.trans hright)

theorem reduction_kernel : RingHom.ker (reduction R A L ε).toRingHom = ideal R A L ε := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hc : ε a ∈ L := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hzero : quotient R A L (algebraMap R A (ε a)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hc)
    have hm : quotient R A L (AugmentationIdeal.AugmentationIdealIntersection.projection R A ε a) ∈ ideal R A L ε :=
      Ideal.mem_map_of_mem _ (AugmentationIdeal.AugmentationIdealIntersection.projection_mem R A ε a)
    rw [AugmentationIdeal.AugmentationIdealIntersection.projection_apply, map_sub, hzero, sub_zero] at hm
    exact hm
  · rw [ideal, Ideal.map_le_iff_le_comap]
    intro a ha
    change reduction R A L ε (quotient R A L a) = 0
    rw [reduction_quotient, show ε a = 0 from ha, map_zero]

variable (δ : DividedPowers (RingHom.ker ε.toRingHom))

def dividedPowers : DividedPowers (ideal R A L ε) :=
  DividedPowers.Quotient.dividedPowers δ (AugmentationIdeal.AugmentationIdealIntersection.isSubDPIdeal R A ε L δ)

theorem quotient_isDPMorphism : DividedPowers.IsDPMorphism δ (AugmentationCoefficientQuotient.dividedPowers R A L ε δ)
    (quotient R A L).toRingHom :=
  DividedPowers.Quotient.isDPMorphism δ (AugmentationIdeal.AugmentationIdealIntersection.isSubDPIdeal R A ε L δ)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.AugmentationCoefficient.AugmentationCoefficientQuotient
