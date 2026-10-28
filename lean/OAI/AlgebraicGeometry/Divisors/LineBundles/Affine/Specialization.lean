import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ClosedSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the finite specialization cycle of an integral affine support

The regular parameter t has a finite effective divisor on the integral
deformation. Its support lies on t = 0. The proved special-fiber isomorphism
therefore transports this actual divisor, without discarding coefficients,
to a finite cycle on the normal cone. Descent modulo rational equivalence
and refined Gysin are further steps.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

universe u
variable {R : Type u} [CommRing R]

/-- The regular section on Spec R[t,I/t] represented by the parameter t. -/
def affineDeformationParameterSection (I : Ideal R) : Γ(Deformation.ClosedSupport.BundleCycles.affineDeformation I, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).inv (Deformation.Iff.BundleCycles.deformationParameter I)

/-- The actual quotient map onto the normal cone, via the special-fiber comparison. -/
def normalConeFiberRingMap (I : Ideal R) : Deformation.Iff.BundleCycles.deformationAlgebra I →+* Normal.Cone.BundleCycles.NormalConeRing I :=
  (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.toRingHom.comp (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I))

theorem normalConeFiberRingMap_surjective (I : Ideal R) :
    Function.Surjective (normalConeFiberRingMap I) :=
  (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.surjective.comp Ideal.Quotient.mk_surjective

theorem normalConeFiberRingMap_ker (I : Ideal R) :
    RingHom.ker (normalConeFiberRingMap I) = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := by
  ext p
  change (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) p) = 0 ↔ _
  rw [map_eq_zero_iff _ (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv I).symm.injective,
    Ideal.Quotient.eq_zero_iff_mem]

/-- Closed inclusion of the actual affine normal cone into the deformation. -/
def normalConeFiberInclusion (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I ⟶ Deformation.ClosedSupport.BundleCycles.affineDeformation I :=
  Spec.map (CommRingCat.ofHom (normalConeFiberRingMap I))

instance normalConeFiberInclusion_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion (normalConeFiberInclusion I) :=
  IsClosedImmersion.spec_of_surjective _ (normalConeFiberRingMap_surjective I)

/-- The cone is exactly the vanishing locus of t in the deformation. -/
theorem normalConeFiberInclusion_range (I : Ideal R) :
    Set.range (normalConeFiberInclusion I) =
      (Deformation.ClosedSupport.BundleCycles.affineDeformation I |>.basicOpen (affineDeformationParameterSection I) : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I))ᶜ := by
  let A : CommRingCat := .of (Deformation.Iff.BundleCycles.deformationAlgebra I)
  let B : CommRingCat := .of (Normal.Cone.BundleCycles.NormalConeRing I)
  let g : A ⟶ B := CommRingCat.ofHom (normalConeFiberRingMap I)
  have hk : RingHom.ker g.hom = Deformation.Iff.BundleCycles.deformationSpecialIdeal I := normalConeFiberRingMap_ker I
  change Set.range (PrimeSpectrum.comap g.hom) = _
  rw [range_comap_of_surjective _ _ (normalConeFiberRingMap_surjective I), hk]
  change PrimeSpectrum.zeroLocus (Deformation.Iff.BundleCycles.deformationSpecialIdeal I) =
    ((Spec A).basicOpen ((Scheme.ΓSpecIso A).inv (Deformation.Iff.BundleCycles.deformationParameter I)) : Set (Spec A))ᶜ
  rw [basicOpen_eq_of_affine]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Deformation.Iff.BundleCycles.deformationParameter I} ≤ x.asIdeal ↔ ¬Deformation.Iff.BundleCycles.deformationParameter I ∉ x.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := x.asIdeal)).trans not_not.symm

variable [IsDomain R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
theorem affineDeformationParameterSection_ne_zero (I : Ideal R) :
    affineDeformationParameterSection I ≠ 0 := by
  intro h
  have ht : Deformation.Iff.BundleCycles.deformationParameter I ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp (Deformation.Iff.BundleCycles.deformationParameter_regular I)
  apply ht
  have he := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom h
  have hzero : (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom 0 = 0 :=
    map_zero (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra I))).hom.hom
  simp only [affineDeformationParameterSection, Iso.inv_hom_id_apply] at he
  exact he.trans hzero

/-- The finite effective divisor of the actual parameter on the integral deformation. -/
def affineDeformationParameterDivisor (I : Ideal R) : Deformation.ClosedSupport.BundleCycles.affineDeformation I →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Deformation.ClosedSupport.BundleCycles.affineDeformation I) (affineDeformationParameterSection I)

theorem affineDeformationParameterDivisor_nonnegative (I : Ideal R) (x : Deformation.ClosedSupport.BundleCycles.affineDeformation I) :
    0 ≤ affineDeformationParameterDivisor I x :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (affineDeformationParameterSection_ne_zero I) x

/-- All divisor coefficients occur on the actual closed normal-cone fiber. -/
theorem affineDeformationParameterDivisor_support (I : Ideal R) :
    ((affineDeformationParameterDivisor I).support : Set (Deformation.ClosedSupport.BundleCycles.affineDeformation I)) ⊆
      Set.range (normalConeFiberInclusion I) := by
  rw [normalConeFiberInclusion_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

/-- The point embedding induced by the normal-cone closed immersion. -/
def normalConeFiberPointEmbedding (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I ↪ Deformation.ClosedSupport.BundleCycles.affineDeformation I :=
  ⟨normalConeFiberInclusion I, (normalConeFiberInclusion I).isClosedEmbedding.injective⟩

/-- The finite specialization cycle on the normal cone of an integral affine scheme. -/
def affineSpecializationCycle (I : Ideal R) : Normal.Cone.BundleCycles.affineNormalCone I →₀ ℤ :=
  Finsupp.comapDomain (normalConeFiberPointEmbedding I) (affineDeformationParameterDivisor I)
    (normalConeFiberPointEmbedding I).injective.injOn

@[simp]
theorem affineSpecializationCycle_apply (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I) :
    affineSpecializationCycle I x = affineDeformationParameterDivisor I (normalConeFiberInclusion I x) := rfl

/-- Re-embedding the cone cycle recovers the whole parameter divisor, coefficient by coefficient. -/
theorem affineSpecializationCycle_push (I : Ideal R) :
    Finsupp.embDomain (normalConeFiberPointEmbedding I) (affineSpecializationCycle I) =
      affineDeformationParameterDivisor I :=
  Finsupp.embDomain_comapDomain (affineDeformationParameterDivisor_support I)

theorem affineSpecializationCycle_nonnegative (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I) :
    0 ≤ affineSpecializationCycle I x := affineDeformationParameterDivisor_nonnegative I _

/-- Every codimension-one specialization coefficient is the actual finite
local length of the quotient by t on the deformation. -/
theorem affineSpecializationCycle_coeff_length (I : Ideal R) (x : Normal.Cone.BundleCycles.affineNormalCone I)
    (hx : coheight (normalConeFiberInclusion I x) = 1) :
    affineSpecializationCycle I x =
      ((Module.length ((Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.stalk (normalConeFiberInclusion I x))
        (((Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.stalk (normalConeFiberInclusion I x)) ⧸
          Ideal.span {(Deformation.ClosedSupport.BundleCycles.affineDeformation I).presheaf.germ ⊤ (normalConeFiberInclusion I x)
            (by trivial) (affineDeformationParameterSection I)})).toNat : ℤ) :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ (affineDeformationParameterSection_ne_zero I) _ hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.Specialization.BundleCycles
