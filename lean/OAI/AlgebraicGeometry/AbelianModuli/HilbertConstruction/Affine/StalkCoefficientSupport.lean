import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkQuotientZeroSection
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Stalk Coefficient Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoefficientSupport

noncomputable section

/-! An affine coefficient map from the spectrum of the stalk at a rational section can map to that section only if its kernel contains the maximal ideal. In particular, the actual field-valued point attached to a different prime is not the rational zero point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem affine_stalk_coefficient_maximal_le_kernel_of_rational_zero
    {K B : Type u} [Field K] [CommRing B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    [IsLocalRing Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤)]
    (φ : Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) →+* B)
    (hzero : let j : Spec (.of B) ⟶ X :=
        QuotientCoefficientMap.affineCoordinateMap φ ≫ X.fromSpecStalk (z (IsLocalRing.closedPoint K));
      j = (j ≫ p) ≫ z) :
    IsLocalRing.maximalIdeal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) ≤ RingHom.ker φ := by
  let x := z (IsLocalRing.closedPoint K)
  let O := X.presheaf.stalk x
  let S := Spec O
  let R := Γ(S, ⊤)
  let j : Spec (.of B) ⟶ S := QuotientCoefficientMap.affineCoordinateMap φ
  let q : O ⟶ .of B := Spec.preimage j
  let e : Γ(S, ⊤) ≅ O := Scheme.ΓSpecIso O
  have hc : e.hom ≫ q = CommRingCat.ofHom φ := by
    apply Spec.map_injective
    calc
      Spec.map (e.hom ≫ q) = Spec.map q ≫ Spec.map e.hom := Spec.map_comp _ _
      _ = j ≫ S.isoSpec.hom := congrArg₂ (fun v w => v ≫ w)
        (Spec.map_preimage j) (Scheme.isoSpec_Spec_hom O).symm
      _ = Spec.map (CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j)) :=
        (QuotientCoefficientMap.specBaseCoefficientMap_specMap j).symm
      _ = Spec.map (CommRingCat.ofHom φ) :=
        congrArg (fun v : R →+* B => Spec.map (CommRingCat.ofHom v))
          (QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap φ)
  let er := Rational.PointResidue.rationalPointResidueIso p z hz
  let t : Spec (.of B) ⟶ Spec (X.residueField x) :=
    ((j ≫ X.fromSpecStalk x) ≫ p) ≫ Spec.map er.hom
  have hfactor : Spec.map q ≫ X.fromSpecStalk x = t ≫ X.fromSpecResidueField x := by
    calc
      _ = j ≫ X.fromSpecStalk x := congrArg (fun v => v ≫ X.fromSpecStalk x) (Spec.map_preimage j)
      _ = ((j ≫ X.fromSpecStalk x) ≫ p) ≫ z := hzero
      _ = ((j ≫ X.fromSpecStalk x) ≫ p) ≫ (Spec.map er.hom ≫ X.fromSpecResidueField x) :=
        congrArg (fun v => ((j ≫ X.fromSpecStalk x) ≫ p) ≫ v)
          (Rational.PointResidue.rationalPointResidueIso_factor p z hz).symm
      _ = t ≫ X.fromSpecResidueField x := (Category.assoc _ _ _).symm
  have : IsLocalHom e.hom.hom := IsLocalHom.of_surjective e.hom.hom e.commRingCatIsoToRingEquiv.surjective
  intro r hr
  have he : e.hom r ∈ IsLocalRing.maximalIdeal O :=
    IsLocalRing.map_maximalIdeal_le e.hom.hom (Ideal.mem_map_of_mem e.hom.hom hr)
  exact (ConcreteCategory.congr_hom hc r).symm.trans
    (StalkQuotientZeroSection.stalk_function_zero_of_residue_factor X x q t hfactor (e.hom r) he)

theorem affine_stalk_primeResidue_ne_rational_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    [IsLocalRing Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤)]
    (v : PrimeSpectrum Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤))
    (hv : v ≠ IsLocalRing.closedPoint Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤)) :
    let j : Spec (.of v.asIdeal.ResidueField) ⟶ X :=
      QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤)
        v.asIdeal.ResidueField) ≫ X.fromSpecStalk (z (IsLocalRing.closedPoint K));
    j ≠ (j ≫ p) ≫ z := by
  dsimp only
  intro hzero
  have h := affine_stalk_coefficient_maximal_le_kernel_of_rational_zero p z hz
    (algebraMap Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) v.asIdeal.ResidueField) hzero
  have hm : IsLocalRing.maximalIdeal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) ≤ v.asIdeal :=
    (congrArg (fun I => IsLocalRing.maximalIdeal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) ≤ I)
      v.asIdeal.ker_algebraMap_residueField).mp h
  apply hv
  apply PrimeSpectrum.ext
  exact le_antisymm (IsLocalRing.le_maximalIdeal v.2.ne_top) hm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoefficientSupport
