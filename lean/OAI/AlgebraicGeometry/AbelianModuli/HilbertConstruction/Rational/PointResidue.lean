import Mathlib.AlgebraicGeometry.ResidueField

/-! # Point Residue -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue

noncomputable section

/-! A rational point identifies its residue field with the ground field, without an algebraic-closure hypothesis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def rationalPointResidueIso {K : Type u} [Field K] {S : Scheme.{u}}
    (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ p = 𝟙 _) :
    S.residueField (s (IsLocalRing.closedPoint K)) ≅ .of K := by
  let a := S.descResidueField (Scheme.stalkClosedPointTo s)
  let b := Spec.preimage (S.fromSpecResidueField (s (IsLocalRing.closedPoint K)) ≫ p)
  have hab : b ≫ a = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, Spec.map_preimage, ← Category.assoc,
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, hs]
  have ha : Function.Bijective a := ⟨a.hom.injective, fun k =>
    ⟨b k, ConcreteCategory.congr_hom hab k⟩⟩
  have : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr ha
  exact asIso a

@[reassoc]
theorem rationalPointResidueIso_factor {K : Type u} [Field K] {S : Scheme.{u}}
    (p : S ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ S) (hs : s ≫ p = 𝟙 _) :
    Spec.map (rationalPointResidueIso p s hs).hom ≫
      S.fromSpecResidueField (s (IsLocalRing.closedPoint K)) = s :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PointResidue
