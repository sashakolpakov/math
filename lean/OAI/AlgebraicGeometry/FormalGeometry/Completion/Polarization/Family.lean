import OAI.AlgebraicGeometry.FormalGeometry.Completion.SchemePointPicardPairing

/-! # Family -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.Family

noncomputable section

/-! The actual polarization family is additive in its parameter.
Every translate differs from it by a line class from the test scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]

def polarizationFamilyClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A) :
    Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :=
  SchemePointPicardPairing.Construction.schemePointPicardPairing A L (T ⊗ A) (Additive.ofMul (fst T A ≫ a)) (Additive.ofMul (snd T A))

theorem polarizationFamilyClass_pullback (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) (a : T ⟶ A) :
    SchemePointPicardPairing.Construction.additivePicardPullback (j ⊗ₘ 𝟙 A).left (polarizationFamilyClass A L a) =
      polarizationFamilyClass A L (j ≫ a) := by
  unfold polarizationFamilyClass
  rw [SchemePointPicardPairing.Construction.schemePointPicardPairing_pullback]
  simp only [toMul_ofMul, tensorHom_fst_assoc, tensorHom_snd, Category.comp_id]

theorem polarizationFamilyClass_mul (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (a b : T ⟶ A) :
    polarizationFamilyClass A L (a * b) = polarizationFamilyClass A L a + polarizationFamilyClass A L b := by
  unfold polarizationFamilyClass
  rw [MonObj.comp_mul]
  change SchemePointPicardPairing.Construction.schemePointPicardPairing A L (T ⊗ A)
      (Additive.ofMul (fst T A ≫ a) + Additive.ofMul (fst T A ≫ b)) (Additive.ofMul (snd T A)) = _
  rw [map_add, LinearMap.add_apply]

theorem polarizationFamilyClass_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K))) :
    polarizationFamilyClass A L (1 : T ⟶ A) = 0 := by
  unfold polarizationFamilyClass
  rw [MonObj.comp_one]
  change SchemePointPicardPairing.Construction.schemePointPicardPairing A L (T ⊗ A) 0 (Additive.ofMul (snd T A)) = 0
  rw [map_zero, LinearMap.zero_apply]

def polarizationFamilyHom (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (T : Over (Spec (CommRingCat.of K))) :
    Additive (T ⟶ A) →+ Additive (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) where
  toFun a := polarizationFamilyClass A L a.toMul
  map_zero' := polarizationFamilyClass_one A L T
  map_add' a b := polarizationFamilyClass_mul A L a.toMul b.toMul

omit [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] in
def polarizationTestTranslation {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A) :
    T ⊗ A ⟶ T ⊗ A :=
  lift (fst T A) ((fst T A ≫ a) * snd T A)

theorem polarizationFamilyClass_translated (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    {T : Over (Spec (CommRingCat.of K))} (x a : T ⟶ A) :
    SchemePointPicardPairing.Construction.additivePicardPullback (polarizationTestTranslation A a).left (polarizationFamilyClass A L x) =
      SchemePointPicardPairing.Construction.additivePicardPullback (fst T A).left
        (SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul x) (Additive.ofMul a)) +
          polarizationFamilyClass A L x := by
  unfold polarizationFamilyClass
  rw [SchemePointPicardPairing.Construction.schemePointPicardPairing_pullback, SchemePointPicardPairing.Construction.schemePointPicardPairing_pullback]
  simp only [toMul_ofMul, polarizationTestTranslation, ← Category.assoc, lift_fst, lift_snd]
  change SchemePointPicardPairing.Construction.schemePointPicardPairing A L (T ⊗ A) (Additive.ofMul (fst T A ≫ x))
      (Additive.ofMul (fst T A ≫ a) + Additive.ofMul (snd T A)) = _
  rw [map_add]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.Family
