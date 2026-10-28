import OAI.ArithmeticGeometry.Descent.CMVariety.RelativeGenericSmooth
import OAI.ArithmeticGeometry.Descent.CMVariety.AbelianCoefficientComparison
import Mathlib.Algebra.CharP.Algebra

/-! # Smooth Coefficient Parameter -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothCoefficientParameter.Abelian

noncomputable section

/-!
An actual finite coefficient extension inside the complex numbers has a
smooth open neighborhood over its original characteristic-zero parameter.
The evaluation point factors through that neighborhood.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affine_functionField_charZero
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] :
    CharZero (Spec (CommRingCat.of R)).functionField := by
  let X := Spec (CommRingCat.of R)
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let ι : R →+* X.functionField :=
    (X.germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hι : Function.Injective ι :=
    (X.germToFunctionField_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  exact (RingHom.charZero_iff hι).mp inferInstance

theorem spec_map_genericPoint_of_injective
    {R T : Type} [CommRing R] [CommRing T] [IsDomain R] [IsDomain T]
    (φ : R →+* T) (hφ : Function.Injective φ) :
    (Spec.map (CommRingCat.ofHom φ)) (genericPoint (Spec (CommRingCat.of T))) =
      genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  exact (RingHom.injective_iff_ker_eq_bot φ).mp hφ

theorem complex_spec_map_genericPoint_of_injective
    {R : Type} [CommRing R] [IsDomain R]
    (φ : R →+* ℂ) (hφ : Function.Injective φ) :
    (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint ℂ) =
      genericPoint (Spec (CommRingCat.of R)) := by
  have h : IsLocalRing.closedPoint ℂ = genericPoint (Spec (CommRingCat.of ℂ)) :=
    Subsingleton.elim _ _
  rw [h]
  exact spec_map_genericPoint_of_injective φ hφ

theorem affine_extension_has_relative_smooth_neighborhood
    (R T : Type) [CommRing R] [CommRing T] [IsDomain R] [IsDomain T]
    [CharZero R] [IsNoetherianRing R] [Algebra R T] [Algebra.FiniteType R T]
    [Algebra R ℂ] [Algebra T ℂ] [IsScalarTower R T ℂ]
    (hR : Function.Injective (algebraMap R ℂ))
    (hT : Function.Injective (algebraMap T ℂ)) :
    ∃ U : (Spec (CommRingCat.of T)).Opens,
      IsIntegral U ∧ Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap R T))) ∧
      ∃ q : Spec (CommRingCat.of ℂ) ⟶ U,
        q ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap T ℂ)) := by
  let : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R T))) :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hRT : Function.Injective (algebraMap R T) := by
    intro x y hxy
    apply hR
    simpa only [← IsScalarTower.algebraMap_apply R T ℂ] using
      congrArg (algebraMap T ℂ) hxy
  have hgeneric := spec_map_genericPoint_of_injective (algebraMap R T) hRT
  let : CharZero (Spec (CommRingCat.of R)).functionField :=
    affine_functionField_charZero R
  apply RelativeGenericSmooth.Abelian.generic_complex_point_factors_through_relative_smooth_open
    (Spec.map (CommRingCat.ofHom (algebraMap R T))) hgeneric
    (Spec.map (CommRingCat.ofHom (algebraMap T ℂ)))
  exact complex_spec_map_genericPoint_of_injective (algebraMap T ℂ) hT

theorem finite_coefficient_extension_has_relative_smooth_neighborhood
    (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Algebra R ℂ] (hR : Function.Injective (algebraMap R ℂ)) (s : (Finset ℂ)ᵒᵖ) :
    ∃ U : (Spec (CommRingCat.of (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop))).Opens,
      IsIntegral U ∧ Smooth (U.ι ≫ FiniteCoefficientDiagram.Abelian.finiteCoefficientBaseMap R ℂ s.unop) ∧
      ∃ q : Spec (CommRingCat.of ℂ) ⟶ U,
        q ≫ U.ι = AbelianCoefficientComparison.coefficientInclusion R ℂ s :=
  affine_extension_has_relative_smooth_neighborhood R (FiniteCoefficientDiagram.Abelian.finiteCoefficientAlgebra R ℂ s.unop)
    hR Subtype.val_injective

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothCoefficientParameter.Abelian
