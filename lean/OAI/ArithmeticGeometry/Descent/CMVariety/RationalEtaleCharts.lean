import OAI.ArithmeticGeometry.Descent.CMVariety.AffineCoordinates
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Rational Etale Charts -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.RationalEtaleCharts.Abelian

noncomputable section

/-! Etale coordinates around rational-scheme complex points, constructed
from ordinary algebraic smoothness. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem affine_point_has_rational_etale_neighborhood
    {A : Type} [CommRing A] [Algebra ℚ A] [Algebra.Smooth ℚ A]
    (x : A →ₐ[ℚ] ℂ) :
    ∃ (Y : Scheme) (q : Y ⟶ Spec (CommRingCat.of ℚ))
      (j : Y ⟶ Spec (CommRingCat.of A)) (y : OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y)
      (n : ℕ) (u : Y ⟶ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).left),
      IsOpenImmersion j ∧ Etale u ∧ LocallyQuasiFinite u ∧
      j ≫ (AffineCoefficientObjects.Abelian.affineCoefficientObject ℚ A).hom = q ∧
      y ≫ j = Spec.map (CommRingCat.ofHom x.toRingHom) ∧
      u ≫ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).hom = q := by
  let p := RingHom.ker x.toRingHom
  have : p.IsPrime := RingHom.ker_isPrime x.toRingHom
  obtain ⟨a, ha, n, aPoly, tower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := ℚ) (p := p)
  let B := Localization.Away a
  let : Algebra (MvPolynomial (Fin n) ℚ) B := aPoly
  let : IsScalarTower ℚ (MvPolynomial (Fin n) ℚ) B := tower
  have : Algebra.IsStandardEtale (MvPolynomial (Fin n) ℚ) B := hEtale
  let j := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q := (AffineCoefficientObjects.Abelian.affineCoefficientObject ℚ B).hom
  let u := Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) ℚ) B))
  let yRing : B →ₐ[ℚ] ℂ := IsLocalization.Away.liftAlgHom (f := x) a
    (isUnit_iff_ne_zero.mpr ha)
  let y := Spec.map (CommRingCat.ofHom yRing.toRingHom)
  have hj : IsOpenImmersion j := IsOpenImmersion.of_isLocalization a
  have hu : Etale u := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  have hqf : LocallyQuasiFinite u := (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
    (RingHom.quasiFinite_algebraMap.mpr inferInstance)
  refine ⟨Spec (CommRingCat.of B), q, j, y, n, u, hj, hu, hqf, ?_, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ B))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom
      (IsScalarTower.algebraMap_eq ℚ A B).symm)
  · change Spec.map (CommRingCat.ofHom yRing.toRingHom) ≫ j = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom
      (IsLocalization.Away.lift_comp a (isUnit_iff_ne_zero.mpr ha)))
  · change Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial (Fin n) ℚ) B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (MvPolynomial (Fin n) ℚ))) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom
      (IsScalarTower.algebraMap_eq ℚ (MvPolynomial (Fin n) ℚ) B).symm)

theorem smooth_point_has_rational_etale_neighborhood
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [Smooth f]
    (p : OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) :
    ∃ (Y : Scheme) (q : Y ⟶ Spec (CommRingCat.of ℚ))
      (j : Y ⟶ X) (y : OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y)
      (n : ℕ) (u : Y ⟶ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).left),
      IsOpenImmersion j ∧ Etale u ∧ LocallyQuasiFinite u ∧
      j ≫ f = q ∧ y ≫ j = p ∧ u ≫ (AffineCoordinates.Abelian.rationalAffineSpace (Fin n)).hom = q := by
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) from trivial)
  let A := Γ(X, U)
  let : Algebra ℚ A := OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let i := hU.fromSpec
  have : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  have hi : i ≫ f = (AffineCoefficientObjects.Abelian.affineCoefficientObject ℚ A).hom :=
    (OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU).symm
  have hs : Smooth (AffineCoefficientObjects.Abelian.affineCoefficientObject ℚ A).hom := by
    rw [← hi]
    exact inferInstanceAs (Smooth (hU.fromSpec ≫ f))
  have : Algebra.Smooth ℚ A := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)
  have hrange : Set.range p ⊆ Set.range i := by
    rintro z ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint ℂ)]
    change p (IsLocalRing.closedPoint ℂ) ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hpU
  let pA := IsOpenImmersion.lift i p hrange
  have hpA : pA ≫ i = p := IsOpenImmersion.lift_fac _ _ _
  let xRing := (Spec.preimage pA).hom
  let x : A →ₐ[ℚ] ℂ :=
    { xRing with commutes' := fun c =>
      DFunLike.congr_fun (show xRing.comp (algebraMap ℚ A) = algebraMap ℚ ℂ from
        Subsingleton.elim _ _) c }
  obtain ⟨Y, q, j, y, n, u, hj, hu, hqf, hjq, hyj, huq⟩ :=
    affine_point_has_rational_etale_neighborhood x
  have : IsOpenImmersion j := hj
  refine ⟨Y, q, j ≫ i, y, n, u, inferInstance, hu, hqf, ?_, ?_, huq⟩
  · rw [Category.assoc, hi, hjq]
  · rw [← Category.assoc, hyj]
    have hx : Spec.map (CommRingCat.ofHom x.toRingHom) = pA := Spec.map_preimage pA
    rw [hx, hpA]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.RationalEtaleCharts.Abelian
