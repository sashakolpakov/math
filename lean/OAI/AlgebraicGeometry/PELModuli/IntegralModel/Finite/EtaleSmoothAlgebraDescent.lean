import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothFromDifferentialCoordinates
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.DifferentialBasisNeighborhood
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Etale Smooth Algebra Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSmoothAlgebraDescent

noncomputable section

section

/-! Smoothness descends through a finite faithfully flat etale
extension. Local differential bases construct actual smooth coordinates. -/

open TensorProduct KaehlerDifferential _root_.Module

theorem smooth_algebra_of_finite_etale_cover
    (R A B : Type) [CommRing R] [IsNoetherianRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.FaithfullyFlat A B] [Module.Finite A B]
    [Algebra.Etale A B] [Algebra.Smooth R B] : Algebra.Smooth R A := by
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.Flat A Ω[A⁄R] := SmoothEtaleDifferentials.differentials_flat_of_faithfully_flat_etale_cover R A B
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun p => ?_), inferInstance⟩
  obtain ⟨g, hg, ι, hι, a, b, hb⟩ := DifferentialBasisNeighborhood.exists_differential_basis_neighborhood R A p.asIdeal
  have : Finite ι := hι
  let Ag := Localization.Away g
  let Bg := Ag ⊗[A] B
  let : Algebra B Bg := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B Bg := IsScalarTower.to₁₃₄ R A B Bg
  have : IsLocalization.Away (algebraMap A B g) Bg := inferInstance
  have : Algebra.Smooth B Bg := Algebra.Smooth.of_isLocalization_Away (algebraMap A B g)
  have : Algebra.Smooth R Bg := Algebra.Smooth.comp R B Bg
  have hs : Algebra.Smooth R Ag :=
    SmoothFromDifferentialCoordinates.smooth_of_differential_coordinates_and_finite_etale_cover R Ag Bg
      (fun i => algebraMap A Ag (a i)) b hb
  exact Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hs hg

end

/-! Smoothness of a scheme morphism descends through a finite etale
surjective source cover, by the constructed affine coordinate criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smooth_of_finite_etale_cover_affine
    {X Y S : Scheme.{0}} [IsAffine Y] [IsAffine S] [IsLocallyNoetherian S]
    (q : X ⟶ Y) (f : Y ⟶ S) [IsFinite q] [Etale q] [Surjective q]
    [LocallyOfFiniteType f] [Smooth (q ≫ f)] : Smooth f := by
  have : IsAffine X := isAffine_of_isAffineHom q
  let R := Γ(S, ⊤)
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra R A := f.appTop.hom.toAlgebra
  let : Algebra A B := q.appTop.hom.toAlgebra
  let : Algebra R B := (q.appTop.hom.comp f.appTop.hom).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite A B := q.finite_appTop
  have : Module.FaithfullyFlat A B :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine q).mp ⟨inferInstance, inferInstance⟩
  have : Algebra.Etale A B := HasRingHomProperty.appTop (P := @Etale) q inferInstance
  have : Algebra.FiniteType R A := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : Algebra.Smooth R B := HasRingHomProperty.appTop (P := @Smooth) (q ≫ f) inferInstance
  have h : f.appTop.hom.Smooth := smooth_algebra_of_finite_etale_cover R A B
  have : Smooth (Spec.map f.appTop) := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr h
  have heq : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

theorem smooth_of_finite_etale_cover
    {X Y S : Scheme.{0}} [IsLocallyNoetherian S]
    (q : X ⟶ Y) (f : Y ⟶ S) [IsFinite q] [Etale q] [Surjective q]
    [LocallyOfFiniteType f] [Smooth (q ≫ f)] : Smooth f := by
  constructor
  intro U hU V hV e
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Surjective (q ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q V).flip inferInstance
  have : Smooth ((q ∣_ V) ≫ f.resLE U V e) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    infer_instance
  have : Smooth (f.resLE U V e) := smooth_of_finite_etale_cover_affine (q ∣_ V) (f.resLE U V e)
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V e)).mp
      (HasRingHomProperty.appTop (P := @Smooth) (f.resLE U V e) inferInstance)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.EtaleSmoothAlgebraDescent
