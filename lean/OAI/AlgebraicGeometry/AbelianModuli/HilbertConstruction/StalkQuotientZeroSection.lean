import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Stalk Quotient Zero Section -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkQuotientZeroSection

noncomputable section

/-! A quotient of the actual local ring that factors through a rational point contains the maximal ideal. Thus a quotient contained in that maximal ideal and sent scheme-theoretically to the point is precisely its residue field quotient. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem stalk_quotient_contains_maximal_of_residue_factor
    (X : Scheme.{u}) (x : X) (I : Ideal (X.presheaf.stalk x))
    (t : Spec (.of ((X.presheaf.stalk x) ⧸ I)) ⟶ Spec (X.residueField x))
    (h : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk x =
      t ≫ X.fromSpecResidueField x) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ I := by
  let q : X.presheaf.stalk x ⟶ .of ((X.presheaf.stalk x) ⧸ I) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  let φ : X.residueField x ⟶ .of ((X.presheaf.stalk x) ⧸ I) := Spec.preimage t
  have hφ : X.residue x ≫ φ = q := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    apply (cancel_mono (X.fromSpecStalk x)).mp
    exact (Category.assoc t (Spec.map (X.residue x)) (X.fromSpecStalk x)).trans h.symm
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hz : X.residue x r = 0 := (IsLocalRing.residue_eq_zero_iff r).mpr hr
  exact (ConcreteCategory.congr_hom hφ r).symm.trans
    ((congrArg φ.hom hz).trans (map_zero φ.hom))

theorem stalk_quotient_eq_maximal_of_rational_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X) (hz : z ≫ p = 𝟙 _)
    (I : Ideal (X.presheaf.stalk (z (IsLocalRing.closedPoint K))))
    (hI : I ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk (z (IsLocalRing.closedPoint K))))
    (hzero : let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
        X.fromSpecStalk (z (IsLocalRing.closedPoint K))
      j = (j ≫ p) ≫ z) :
    I = IsLocalRing.maximalIdeal (X.presheaf.stalk (z (IsLocalRing.closedPoint K))) := by
  let x := z (IsLocalRing.closedPoint K)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ X.fromSpecStalk x
  let e := Rational.PointResidue.rationalPointResidueIso p z hz
  let t : Spec (.of ((X.presheaf.stalk x) ⧸ I)) ⟶ Spec (X.residueField x) :=
    (j ≫ p) ≫ Spec.map e.hom
  apply le_antisymm hI
  apply stalk_quotient_contains_maximal_of_residue_factor X x I t
  calc
    j = (j ≫ p) ≫ z := hzero
    _ = (j ≫ p) ≫ (Spec.map e.hom ≫ X.fromSpecResidueField x) :=
      congrArg (fun a : Spec (.of K) ⟶ X => (j ≫ p) ≫ a)
        (Rational.PointResidue.rationalPointResidueIso_factor p z hz).symm
    _ = t ≫ X.fromSpecResidueField x := (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StalkQuotientZeroSection
