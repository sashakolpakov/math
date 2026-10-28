import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePointProjection
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Finite Birational -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteBirational.Constructions.Algebraization

noncomputable section

section

/-!
# Integral and residue-field consequences of a finite graph projection
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem isIntegral_of_reduced_universallyInjective_surjective
    {X Y : Scheme} [IsReduced X] [IsIntegral Y]
    (f : X ⟶ Y) [UniversallyInjective f] [Surjective f] [UniversallyClosed f] : IsIntegral X := by
  let e : X ≃ₜ Y := (Equiv.ofBijective f ⟨f.injective, f.surjective⟩).toHomeomorphOfContinuousClosed
    f.continuous f.isClosedMap
  let : IrreducibleSpace X := e.irreducibleSpace_iff.mpr inferInstance
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem residueFieldMap_bijective_of_universallyInjective_complex
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) [UniversallyInjective f.left] (x : X.left) :
    Function.Bijective (f.left.residueFieldMap x) := by
  let K := Y.left.residueField (f.left x)
  let L := X.left.residueField x
  let σ : ℂ →+* K := (Spec.preimage (Y.left.fromSpecResidueField (f.left x) ≫ Y.hom)).hom
  let : CharZero K := charZero_of_injective_ringHom σ.injective
  let : Algebra K L := (f.left.residueFieldMap x).hom.toAlgebra
  have hcrit : Function.Injective f.left ∧
      ∀ x, (f.left.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective f.left).out 1 3).mp
      (show UniversallyInjective f.left from inferInstance)
  have hpure : (f.left.residueFieldMap x).hom.IsPurelyInseparable := hcrit.2 x
  let : IsPurelyInseparable K L := hpure
  exact ⟨(f.left.residueFieldMap x).hom.injective,
    IsPurelyInseparable.surjective_algebraMap_of_isSeparable K L⟩

theorem algebraMap_bijective_of_integral_field_embedding
    {R S K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (e : S →ₐ[R] K) (he : Function.Injective e) : Function.Bijective (algebraMap R S) := by
  constructor
  · intro a b hab
    apply IsFractionRing.injective R K
    simpa only [AlgHom.commutes] using congrArg e hab
  · intro s
    have hs : IsIntegral R (e s) := (Algebra.IsIntegral.isIntegral s).map e
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hs
    exact ⟨r, he (by rwa [e.commutes])⟩

end

/-!
# The generic stalk of the finite graph projection
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem genericPoint_map_of_surjective
    {X Y : Scheme} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) [Surjective f] : f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert (genericPoint_spec X).image f.continuous using 1
  rw [image_univ, range_eq_univ.mpr f.surjective, closure_univ]

theorem stalkMap_bijective_of_field_stalks
    {X Y : Scheme} (f : X ⟶ Y) (x : X)
    (hY : IsField (Y.presheaf.stalk (f x))) (hX : IsField (X.presheaf.stalk x))
    (hres : Function.Surjective (f.residueFieldMap x)) :
    Function.Bijective (f.stalkMap x) := by
  let : Field (Y.presheaf.stalk (f x)) := hY.toField
  let : Field (X.presheaf.stalk x) := hX.toField
  refine ⟨(f.stalkMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨r, hr⟩ := hres (X.residue x z)
  obtain ⟨a, ha⟩ := Y.residue_surjective (f x) r
  refine ⟨a, (X.residue x).hom.injective ?_⟩
  have hcomm := congrArg (fun g : Y.presheaf.stalk (f x) ⟶ X.residueField x => g a)
    (Scheme.residue_residueFieldMap f x)
  change f.residueFieldMap x (Y.residue (f x) a) = X.residue x (f.stalkMap x a) at hcomm
  rw [ha, hr] at hcomm
  exact hcomm.symm

theorem generic_stalkMap_bijective
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [UniversallyInjective f.left] [Surjective f.left] :
    Function.Bijective (f.left.stalkMap (genericPoint X.left)) := by
  have hgen := genericPoint_map_of_surjective f.left
  have hfield : IsField (Y.left.presheaf.stalk (f.left (genericPoint X.left))) := by
    rw [hgen]
    exact (inferInstance : Field Y.left.functionField).toIsField
  exact stalkMap_bijective_of_field_stalks f.left (genericPoint X.left)
    hfield (inferInstance : Field X.left.functionField).toIsField
    (residueFieldMap_bijective_of_universallyInjective_complex f _).surjective

theorem isFractionRing_generic_stalk
    (Y : Scheme) [IsIntegral Y] (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (y : Y) (hy : y = genericPoint Y) (hyU : y ∈ U) :
    letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hyU).hom.toAlgebra
    IsFractionRing Γ(Y, U) (Y.presheaf.stalk y) := by
  subst y
  exact functionField_isFractionRing_of_isAffineOpen Y U hU

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteBirational.Constructions.Algebraization
