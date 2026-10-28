import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the affine normal cone in its Rees presentation

For an ideal I of R, the normal-cone algebra is R[It] / I R[It].
The base map and augmentation are induced by constants and evaluation at
degree zero. Their composite is the identity, giving the cone's canonical
closed zero section over Spec(R/I).

This is the affine algebraic construction. The degreewise associated-graded
comparison, gluing over a general closed immersion, deformation space, and
specialization on Chow groups are separate steps still needed for refined Gysin.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {R : Type u} [CommRing R]

/-- Extension of I to its actual Rees algebra. -/
def normalConeIdeal (I : Ideal R) : Ideal (reesAlgebra I) :=
  I.map (algebraMap R (reesAlgebra I))

/-- The standard Rees presentation of the affine normal-cone algebra. -/
abbrev NormalConeRing (I : Ideal R) := (reesAlgebra I) ⧸ normalConeIdeal I

/-- Constants induce the structure map from the closed base R/I. -/
def normalConeBaseMap (I : Ideal R) : R ⧸ I →+* NormalConeRing I :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (normalConeIdeal I)).comp (algebraMap R (reesAlgebra I)))
    (fun _ hr => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) hr))

@[simp]
theorem normalConeBaseMap_mk (I : Ideal R) (r : R) :
    normalConeBaseMap I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (normalConeIdeal I) (algebraMap R (reesAlgebra I) r) := rfl

/-- Degree-zero evaluation on the Rees subalgebra. -/
def reesAugmentation (I : Ideal R) : reesAlgebra I →+* R :=
  Polynomial.constantCoeff.comp (reesAlgebra I).val.toRingHom

@[simp]
theorem reesAugmentation_algebraMap (I : Ideal R) (r : R) :
    reesAugmentation I (algebraMap R (reesAlgebra I) r) = r := by
  simp [reesAugmentation]

/-- The Rees augmentation carries the extended ideal into I. -/
theorem normalConeIdeal_le_augmentation_ker (I : Ideal R) :
    normalConeIdeal I ≤
      RingHom.ker ((Ideal.Quotient.mk I).comp (reesAugmentation I)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change Ideal.Quotient.mk I (reesAugmentation I (algebraMap R (reesAlgebra I) r)) = 0
  rw [reesAugmentation_algebraMap]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- Augmentation of the normal-cone algebra to the closed base. -/
def normalConeAugmentation (I : Ideal R) : NormalConeRing I →+* R ⧸ I :=
  Ideal.Quotient.lift (normalConeIdeal I)
    ((Ideal.Quotient.mk I).comp (reesAugmentation I))
    (fun _ hr => normalConeIdeal_le_augmentation_ker I hr)

@[simp]
theorem normalConeAugmentation_mk (I : Ideal R) (a : reesAlgebra I) :
    normalConeAugmentation I (Ideal.Quotient.mk (normalConeIdeal I) a) =
      Ideal.Quotient.mk I (reesAugmentation I a) := rfl

/-- Constants followed by augmentation are the identity on the base ring. -/
theorem normalConeAugmentation_comp_base (I : Ideal R) :
    (normalConeAugmentation I).comp (normalConeBaseMap I) = RingHom.id (R ⧸ I) := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  change Ideal.Quotient.mk I (reesAugmentation I (algebraMap R (reesAlgebra I) r)) =
    Ideal.Quotient.mk I r
  rw [reesAugmentation_algebraMap]

theorem normalConeBaseMap_injective (I : Ideal R) :
    Function.Injective (normalConeBaseMap I) :=
  (show Function.LeftInverse (normalConeAugmentation I) (normalConeBaseMap I) from
    fun r => DFunLike.congr_fun (normalConeAugmentation_comp_base I) r).injective

theorem normalConeAugmentation_surjective (I : Ideal R) :
    Function.Surjective (normalConeAugmentation I) :=
  (show Function.RightInverse (normalConeBaseMap I) (normalConeAugmentation I) from
    fun r => DFunLike.congr_fun (normalConeAugmentation_comp_base I) r).surjective

/-- The actual affine scheme of the normal cone. -/
def affineNormalCone (I : Ideal R) : Scheme := Spec (CommRingCat.of (NormalConeRing I))

/-- The cone's projection to the closed subscheme Spec(R/I). -/
def affineNormalConeProjection (I : Ideal R) :
    affineNormalCone I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  Spec.map (CommRingCat.ofHom (normalConeBaseMap I))

/-- The zero section defined by the actual augmentation. -/
def affineNormalConeZeroSection (I : Ideal R) :
    Spec (CommRingCat.of (R ⧸ I)) ⟶ affineNormalCone I :=
  Spec.map (CommRingCat.ofHom (normalConeAugmentation I))

theorem affineNormalConeZeroSection_projection (I : Ideal R) :
    affineNormalConeZeroSection I ≫ affineNormalConeProjection I =
      𝟙 (Spec (CommRingCat.of (R ⧸ I))) := by
  let b : CommRingCat.of (R ⧸ I) ⟶ CommRingCat.of (NormalConeRing I) :=
    CommRingCat.ofHom (normalConeBaseMap I)
  let a : CommRingCat.of (NormalConeRing I) ⟶ CommRingCat.of (R ⧸ I) :=
    CommRingCat.ofHom (normalConeAugmentation I)
  have h : b ≫ a = 𝟙 (CommRingCat.of (R ⧸ I)) := by
    apply CommRingCat.hom_ext
    exact normalConeAugmentation_comp_base I
  exact (Spec.map_comp b a).symm.trans
    ((congrArg Spec.map h).trans (Spec.map_id _))

/-- The canonical zero section is a closed immersion. -/
instance affineNormalConeZeroSection_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (affineNormalConeZeroSection I) :=
  IsClosedImmersion.spec_of_surjective _ (normalConeAugmentation_surjective I)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.Cone.BundleCycles
