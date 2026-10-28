import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkQuotientZeroSection

/-! # Stalk Closed Field Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkClosedFieldPoint

noncomputable section

/-! A closed field-valued point of the spectrum of a rational-point stalk has the same ground field, via its actual structure morphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem rationalStalk_closedFieldPoint_structure_isIso
    {K B : Type u} [Field K] [Field B] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (j : Spec (.of B) ⟶ Spec (X.presheaf.stalk (z (IsLocalRing.closedPoint K))))
    [IsClosedImmersion j] :
    IsIso ((j ≫ X.fromSpecStalk (z (IsLocalRing.closedPoint K))) ≫ p) := by
  let x := z (IsLocalRing.closedPoint K)
  let O := X.presheaf.stalk x
  let q : O ⟶ .of B := Spec.preimage j
  let e : Γ(Spec O, ⊤) ≅ O := Scheme.ΓSpecIso O
  have heq : e.hom ≫ q = CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j) := by
    apply Spec.map_injective
    calc
      Spec.map (e.hom ≫ q) = Spec.map q ≫ Spec.map e.hom := Spec.map_comp _ _
      _ = j ≫ (Spec O).isoSpec.hom := congrArg₂ (fun v w => v ≫ w)
        (Spec.map_preimage j) (Scheme.isoSpec_Spec_hom O).symm
      _ = Spec.map (CommRingCat.ofHom (HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap j)) :=
        (Affine.QuotientCoefficientMap.specBaseCoefficientMap_specMap j).symm
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨r, hr⟩ := HilbertConstruction.Spec.CoefficientCechComparison.specBaseCoefficientMap_surjective j y
    exact ⟨e.hom r, (ConcreteCategory.congr_hom heq r).trans hr⟩
  have : IsLocalHom q.hom := IsLocalHom.of_surjective q.hom hq
  let d := X.descResidueField q
  have hd : Function.Bijective d := by
    refine ⟨d.hom.injective, ?_⟩
    intro y
    obtain ⟨r, hr⟩ := hq y
    exact ⟨X.residue x r, (ConcreteCategory.congr_hom (X.residue_descResidueField q) r).trans hr⟩
  have : IsIso d := (ConcreteCategory.isIso_iff_bijective d).mpr hd
  let er := PointResidue.rationalPointResidueIso p z hz
  have hcomp : Spec.map er.hom ≫ (X.fromSpecResidueField x ≫ p) = 𝟙 _ := by
    rw [← Category.assoc, PointResidue.rationalPointResidueIso_factor p z hz, hz]
  have he : X.fromSpecResidueField x ≫ p = (asIso (Spec.map er.hom)).inv := by
    apply (cancel_epi (Spec.map er.hom)).mp
    rw [hcomp]
    simp
  have : IsIso (X.fromSpecResidueField x ≫ p) := by rw [he]; infer_instance
  have hc : (j ≫ X.fromSpecStalk x) ≫ p = Spec.map d ≫ (X.fromSpecResidueField x ≫ p) := by
    rw [← Category.assoc, X.descResidueField_fromSpecResidueField q, Spec.map_preimage]
  rw [hc]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.StalkClosedFieldPoint
