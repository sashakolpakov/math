import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteBirational
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.SmoothNormal
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Finite Normal Iso -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteNormalIso.Constructions.Algebraization

noncomputable section

/-!
# The finite graph projection is an isomorphism

An integral finite source embeds in the target function field using the
inverse generic stalk map. Integral closedness then makes every affine
coordinate-ring map surjective, and hence an isomorphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set

theorem app_bijective_of_finite_generic_stalk
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (hg : Function.Bijective (f.stalkMap (genericPoint X)))
    (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] [IsIntegrallyClosed Γ(Y, U)] :
    Function.Bijective (f.app U) := by
  let x := genericPoint X
  have hgen : f x = genericPoint Y := FiniteBirational.Constructions.Algebraization.genericPoint_map_of_surjective f
  have hyU : f x ∈ U := by
    rw [hgen]
    exact (genericPoint_spec Y).mem_open_set_iff U.isOpen |>.mpr
      ⟨(Classical.arbitrary U).val, mem_univ _, (Classical.arbitrary U).property⟩
  let R := Γ(Y, U)
  let S := Γ(X, f ⁻¹ᵁ U)
  let K := Y.presheaf.stalk (f x)
  have hfield : IsField K := by
    change IsField (Y.presheaf.stalk (f x))
    rw [hgen]
    exact (inferInstance : Field Y.functionField).toIsField
  let : Field K := hfield.toField
  let : Algebra R S := (f.app U).hom.toAlgebra
  let : Algebra.IsIntegral R S := ⟨f.isIntegral_app U hU⟩
  let : Algebra R K := (Y.presheaf.germ U (f x) hyU).hom.toAlgebra
  let : IsFractionRing R K := FiniteBirational.Constructions.Algebraization.isFractionRing_generic_stalk Y U hU (f x) hgen hyU
  let e₀ := RingEquiv.ofBijective (f.stalkMap x).hom hg
  let e : S →ₐ[R] K :=
    { toRingHom := e₀.symm.toRingHom.comp (X.presheaf.germ (f ⁻¹ᵁ U) x hyU).hom
      commutes' := by
        intro r
        change e₀.symm (X.presheaf.germ (f ⁻¹ᵁ U) x hyU (f.app U r)) =
          Y.presheaf.germ U (f x) hyU r
        rw [← f.germ_stalkMap_apply U x hyU]
        exact e₀.symm_apply_apply _ }
  have he : Function.Injective e :=
    e₀.symm.injective.comp (germ_injective_of_isIntegral X x hyU)
  exact FiniteBirational.Constructions.Algebraization.algebraMap_bijective_of_integral_field_embedding e he

theorem isIso_of_finite_universallyInjective_surjective_smooth
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced X.left] [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [UniversallyInjective f.left] [Surjective f.left] :
    IsIso f.left := by
  let : IsIntegral X.left := FiniteBirational.Constructions.Algebraization.isIntegral_of_reduced_universallyInjective_surjective f.left
  have hg := FiniteBirational.Constructions.Algebraization.generic_stalkMap_bijective f
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _)
  intro y
  obtain ⟨U, hU, hyU, _⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.left.isBasis_affineOpens)
      (show y ∈ (⊤ : Y.left.Opens) from trivial)
  change Y.left.Opens at U
  let : Nonempty U := ⟨⟨y, hyU⟩⟩
  let : IsIntegrallyClosed Γ(Y.left, U) := SmoothNormal.Constructions.Algebraization.isIntegrallyClosed_affineOpen_of_smooth_integral Y U hU
  refine ⟨U, hyU, (isIso_morphismRestrict_iff_isIso_app f.left hU).mpr ?_⟩
  exact (ConcreteCategory.isIso_iff_bijective (f.left.app U)).mpr
    (app_bijective_of_finite_generic_stalk f.left hg U hU)

theorem isIso_of_proper_bijective_complex_points
    {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (f : X ⟶ Y) [IsProper f.left]
    (hf : Function.Bijective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)) : IsIso f.left := by
  let : UniversallyInjective f.left := FinitePointProjection.Constructions.Algebraization.universallyInjective_of_injective_complex_points f hf.injective
  let : Surjective f.left :=
    FinitePointProjection.Constructions.Algebraization.surjective_of_surjective_complex_points f f.left.isClosedMap.isClosed_range hf.surjective
  let : IsFinite f.left := FinitePointProjection.Constructions.Algebraization.finite_of_proper_injective_complex_points f hf.injective
  exact isIso_of_finite_universallyInjective_surjective_smooth f

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteNormalIso.Constructions.Algebraization
