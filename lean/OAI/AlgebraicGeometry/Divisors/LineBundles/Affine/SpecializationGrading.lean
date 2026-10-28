import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Transcendence
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization
import OAI.AlgebraicGeometry.DivisorClass.Chern.HeightOneDimension
import OAI.AlgebraicGeometry.Foundations.Scheme.CycleSupports

/-! # Specialization Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading.BundleCycles

noncomputable section

/-!
# LineBundleCycles: dimension grading of affine specialization

A nonzero specialization multiplicity comes from a codimension-one point
on the integral deformation. The height-one dimension theorem and the
proved one-parameter transcendence formula show that its quotient has
exactly the original support's transcendence dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

/-- A surjection identifies the quotient by the inverse-image ideal with the target quotient in transcendence degree. -/
theorem quotient_trdeg_of_surjective {k A B : Type} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Surjective f) (q : Ideal B) :
    Algebra.trdeg k (A ⧸ q.comap f.toRingHom) = Algebra.trdeg k (B ⧸ q) := by
  let g := Ideal.quotientMapₐ q f le_rfl
  exact (trdeg_le_of_injective g Ideal.quotientMap_injective).antisymm
    (trdeg_le_of_surjective g (Ideal.quotientMap_surjective (H := le_rfl) hf))

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R)

/-- Every nonzero specialization coefficient is a codimension-one divisor coefficient. -/
theorem affineSpecializationCycle_coheight (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) : coheight (Specialization.BundleCycles.normalConeFiberInclusion I x) = 1 := by
  by_contra h
  apply hx
  change (Deformation.ClosedSupport.BundleCycles.affineDeformation I).ord
    (RegularDivisor.BundleCycles.globalFunctionFieldElement (Deformation.ClosedSupport.BundleCycles.affineDeformation I) (Specialization.BundleCycles.affineDeformationParameterSection I))
      (Specialization.BundleCycles.normalConeFiberInclusion I x) = 0
  exact Scheme.ord_eq_zero_of_coheight_neq_one h _

/-- The ambient prime of a point on the affine normal-cone fiber. -/
def affineSpecializationAmbientPrime (x : Normal.Cone.BundleCycles.affineNormalCone I) : PrimeSpectrum (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
  Specialization.BundleCycles.normalConeFiberInclusion I x

variable (k : Type) [Field k] [Algebra k R] [Algebra.FiniteType k R]

/-- A height-one prime of the deformation has the original coefficient ring's dimension. -/
theorem deformationHeightOne_trdeg (q : PrimeSpectrum (Deformation.Iff.BundleCycles.deformationAlgebra I)) (hq : q.asIdeal.height = 1) :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    (Algebra.trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ q.asIdeal)).toNat = (Algebra.trdeg k R).toNat := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  have : Algebra.FiniteType k (Deformation.Iff.BundleCycles.deformationAlgebra I) :=
    Deformation.Transcendence.BundleCycles.deformationAlgebra_finiteType_base I k (IsNoetherian.noetherian I)
  have h := DivisorClass.Chern.HeightOneDimension.Construction.finiteType_height_one_trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I) q.asIdeal hq
  rw [Deformation.Transcendence.BundleCycles.deformationAlgebra_trdeg_toNat I k] at h
  omega

/-- The actual nonzero specialization coefficients preserve transcendence dimension. -/
theorem affineSpecializationCycle_dimension (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    (Algebra.trdeg k (Deformation.Iff.BundleCycles.deformationAlgebra I ⧸ (affineSpecializationAmbientPrime I x).asIdeal)).toNat =
      (Algebra.trdeg k R).toNat := by
  apply deformationHeightOne_trdeg I k
  exact (idealHeight_eq_coheight (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))
    (affineSpecializationAmbientPrime I x)).trans (affineSpecializationCycle_coheight I x hx)

/-- The field action on the normal cone is induced by its actual closed-fiber quotient map. -/
abbrev normalConeScalarAlgebra : Algebra k (Normal.Cone.BundleCycles.NormalConeRing I) :=
  @RingHom.toAlgebra k (Normal.Cone.BundleCycles.NormalConeRing I) (by infer_instance) (by infer_instance)
    ((Specialization.BundleCycles.normalConeFiberRingMap I).comp
      ((algebraMap R (Deformation.Iff.BundleCycles.deformationAlgebra I)).comp (algebraMap k R)))

/-- The actual fiber quotient as a homomorphism over the original coefficient field. -/
def normalConeFiberAlgHom :
    letI := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
    letI := normalConeScalarAlgebra I k
    Deformation.Iff.BundleCycles.deformationAlgebra I →ₐ[k] Normal.Cone.BundleCycles.NormalConeRing I := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  let := normalConeScalarAlgebra I k
  exact { Specialization.BundleCycles.normalConeFiberRingMap I with commutes' := fun _ => rfl }

/-- The quotient ring of the normal-cone support itself has the original support's dimension. -/
theorem affineSpecializationCycle_cone_dimension (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : Specialization.BundleCycles.affineSpecializationCycle I x ≠ 0) :
    letI := normalConeScalarAlgebra I k
    (Algebra.trdeg k (Normal.Cone.BundleCycles.NormalConeRing I ⧸ x.asIdeal)).toNat = (Algebra.trdeg k R).toNat := by
  let := Deformation.Transcendence.BundleCycles.deformationScalarAlgebra I k
  let := normalConeScalarAlgebra I k
  have hq := quotient_trdeg_of_surjective (normalConeFiberAlgHom I k)
    (Specialization.BundleCycles.normalConeFiberRingMap_surjective I) x.asIdeal
  exact (congrArg Cardinal.toNat hq).symm.trans (affineSpecializationCycle_dimension I k x hx)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.SpecializationGrading.BundleCycles
