import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuotientCoefficientMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkQuotientZeroSection
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Stalk Quotient Zero Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkQuotientZeroSection

noncomputable section

/-! The coefficient ideal in the global functions of the spectrum of an actual stalk is maximal when its affine quotient maps scheme-theoretically to the rational zero point. The canonical global-functions/stalk isomorphism is retained explicitly. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem stalkSpecGlobalSections_isLocalRing (X : Scheme.{u}) (x : X) :
    IsLocalRing Γ(Spec (X.presheaf.stalk x), ⊤) :=
  (Scheme.ΓSpecIso (X.presheaf.stalk x)).commRingCatIsoToRingEquiv.symm.isLocalRing

theorem stalk_function_zero_of_residue_factor
    (X : Scheme.{u}) (x : X) {B : Type u} [CommRing B]
    (q : X.presheaf.stalk x ⟶ .of B) (t : Spec (.of B) ⟶ Spec (X.residueField x))
    (h : Spec.map q ≫ X.fromSpecStalk x = t ≫ X.fromSpecResidueField x)
    (r : X.presheaf.stalk x) (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    q.hom r = 0 := by
  let φ : X.residueField x ⟶ .of B := Spec.preimage t
  have hφ : X.residue x ≫ φ = q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    apply (cancel_mono (X.fromSpecStalk x)).mp
    exact (Category.assoc t (Spec.map (X.residue x)) (X.fromSpecStalk x)).trans h.symm
  have hz : X.residue x r = 0 := (IsLocalRing.residue_eq_zero_iff r).mpr hr
  exact (ConcreteCategory.congr_hom hφ r).symm.trans
    ((congrArg φ.hom hz).trans (map_zero φ.hom))

theorem affine_stalk_quotient_eq_maximal_of_rational_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    [IsLocalRing Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤)]
    (I : Ideal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤))
    (hI : I ≤ IsLocalRing.maximalIdeal
      Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤))
    (hzero : let j : Spec (.of (Γ(Spec (X.presheaf.stalk
        (z (IsLocalRing.closedPoint K))), ⊤) ⧸ I)) ⟶ X :=
        (QuotientCoefficientMap.affineCoordinateMap (S := Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))))
          (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk (z (IsLocalRing.closedPoint K));
      j = (j ≫ p) ≫ z) :
    I = IsLocalRing.maximalIdeal Γ(Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))), ⊤) := by
  let x := z (IsLocalRing.closedPoint K)
  let O := X.presheaf.stalk x
  let S := Spec O
  let R := Γ(S, ⊤)
  let B := R ⧸ I
  let j : Spec (.of B) ⟶ S := QuotientCoefficientMap.affineCoordinateMap (Ideal.Quotient.mk I)
  let q : O ⟶ .of B := Spec.preimage j
  let e : Γ(S, ⊤) ≅ O := Scheme.ΓSpecIso O
  have hc : e.hom ≫ q = CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    calc
      Spec.map (e.hom ≫ q) = Spec.map q ≫ Spec.map e.hom := Spec.map_comp _ _
      _ = j ≫ S.isoSpec.hom := congrArg₂ (fun v w => v ≫ w)
        (Spec.map_preimage j) (Scheme.isoSpec_Spec_hom O).symm
      _ = Spec.map (CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j)) :=
        (QuotientCoefficientMap.specBaseCoefficientMap_specMap j).symm
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) :=
        congrArg (fun v : R →+* B => Spec.map (CommRingCat.ofHom v))
          (QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap (Ideal.Quotient.mk I))
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
  apply le_antisymm hI
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have he : e.hom r ∈ IsLocalRing.maximalIdeal O :=
    IsLocalRing.map_maximalIdeal_le e.hom.hom (Ideal.mem_map_of_mem e.hom.hom hr)
  exact (ConcreteCategory.congr_hom hc r).symm.trans
    (stalk_function_zero_of_residue_factor X x q t hfactor (e.hom r) he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkQuotientZeroSection
