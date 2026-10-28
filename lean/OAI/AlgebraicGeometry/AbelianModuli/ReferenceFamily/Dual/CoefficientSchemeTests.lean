import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ImmersionLiftFibers
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Coefficient Scheme Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientSchemeTests

noncomputable section

/-! Actual dual-number test schemes over arbitrary coefficient algebras.
The reduction is a surjective closed immersion and the projection is
its retraction; no field or local-ring assumption is made on coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local implicit_reducible] EtaleSplittingAt.EtaleSplitting.affineOver

variable (k C : Type) [CommRing k] [CommRing C] [Algebra k C]

def dualCoefficientOrigin : EtaleSplittingAt.EtaleSplitting.affineOver k C ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) :=
  Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k (DualNumber C) C (TrivSqZeroExt.fstHom k C C)

def dualCoefficientProjection : EtaleSplittingAt.EtaleSplitting.affineOver k (DualNumber C) ⟶ EtaleSplittingAt.EtaleSplitting.affineOver k C :=
  Affine.AlgebraAutomorphismNaturality.affineOverAlgHom k C (DualNumber C) (TrivSqZeroExt.inlAlgHom k C C)

theorem dualCoefficientOrigin_projection : dualCoefficientOrigin k C ≫ dualCoefficientProjection k C = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k C C).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlAlgHom k C C).toRingHom) = 𝟙 (Spec (.of C))
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlAlgHom k C C).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k C C).toRingHom = 𝟙 (CommRingCat.of C) := by
    ext c
    rfl
  rw [h, Spec.map_id]

instance dualCoefficientOrigin_closed : IsClosedImmersion (dualCoefficientOrigin k C).left :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k C C).toRingHom)
    (fun c => ⟨(c, 0), rfl⟩)

instance dualCoefficientOrigin_surjective : Surjective (dualCoefficientOrigin k C).left := by
  let q := (TrivSqZeroExt.fstHom k C C).toRingHom
  have hr : Set.range (PrimeSpectrum.comap q) = Set.univ := by
    rw [range_comap_of_surjective C q (fun c => ⟨(c, 0), rfl⟩)]
    apply Set.eq_univ_of_forall
    intro p z hz
    have hz' : z.fst = 0 := hz
    have hs : z ^ 2 = 0 := by
      rw [pow_two]
      apply TrivSqZeroExt.ext
      · change z.fst * z.fst = 0
        rw [hz', zero_mul]
      · rw [DualNumber.snd_mul, hz', zero_mul, mul_zero, add_zero]
        rfl
    exact p.isPrime.mem_of_pow_mem 2 (hs.symm ▸ p.asIdeal.zero_mem)
  exact ⟨Set.range_eq_univ.mp hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientSchemeTests
