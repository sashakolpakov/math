import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.Family

/-! # Family Bundle -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.FamilyBundle

noncomputable section

/-! An actual representative of the polarization line class, with its
identity-axis trivialization derived from bilinearity. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A)

def polarizationFamilyBundle : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ A).left := (Family.Construction.polarizationFamilyClass A L a).toMul.out

theorem polarizationFamilyBundle_class :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationFamilyBundle A L a) = (Family.Construction.polarizationFamilyClass A L a).toMul :=
  Quotient.out_eq _

theorem polarizationFamilyClass_axis :
    SchemePointPicardPairing.Construction.additivePicardPullback (lift (𝟙 T) (1 : T ⟶ A)).left (Family.Construction.polarizationFamilyClass A L a) = 0 := by
  unfold Family.Construction.polarizationFamilyClass
  rw [SchemePointPicardPairing.Construction.schemePointPicardPairing_pullback]
  simp only [toMul_ofMul, lift_fst_assoc, Category.id_comp, lift_snd]
  exact (SchemePointPicardPairing.Construction.schemePointPicardPairing A L T (Additive.ofMul a)).map_zero

def polarizationFamilyRigidification :
    (Scheme.Modules.pullback (lift (𝟙 T) (1 : T ⟶ A)).left).obj
        (polarizationFamilyBundle A L a).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left := by
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift (𝟙 T) (1 : T ⟶ A)).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationFamilyBundle A L a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass T.left := by
    rw [polarizationFamilyBundle_class]
    exact congrArg Additive.toMul (polarizationFamilyClass_axis A L a)
  exact Classical.choice (Quotient.exact hc)

theorem polarizationFamilyBundle_pullback {U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (polarizationFamilyBundle A L a)) =
      (Family.Construction.polarizationFamilyClass A L (j ≫ a)).toMul := by
  rw [polarizationFamilyBundle_class]
  exact congrArg Additive.toMul (Family.Construction.polarizationFamilyClass_pullback A L j a)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.FamilyBundle
