import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.DefectRestriction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FixedFiber.RegularSections

/-! # Regular Defects -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularDefects

noncomputable section

/-! The actual local morphism defects give original regular sections
on the fixed fiber, and these sections commute with affine restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    {X Y : Over (Spec (.of R))} [Smooth X.hom] [Smooth Y.hom]
    [Smooth (TangentBasePoint.fixedFamilyFiber ℂ R Y).hom] [GrpObj (TangentBasePoint.fixedFamilyFiber ℂ R Y)]
    (f : X ⟶ Y)

def familyMorphismRegularDefect (V U : X.left.affineOpens) (W Z : Y.left.affineOpens)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (a : V.1 ≤ U.1) (b : W.1 ≤ Z.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    Γ((TangentBasePoint.fixedFamilyFiber ℂ R X).left, FixedFiber.CoordinateProjection.fixedFiberAffineOpen R ℂ X V) :=
  FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V (GroupRetractions.familyMorphismConormalDefect R f V U W Z h a b d z)

theorem familyMorphismRegularDefect_restrict
    (V V' U : X.left.affineOpens) (W W' Z : Y.left.affineOpens)
    (t : V'.1 ≤ V.1) (s : W'.1 ≤ W.1)
    (h : V.1 ≤ f.left ⁻¹ᵁ W.1) (h' : V'.1 ≤ f.left ⁻¹ᵁ W'.1)
    (a : V.1 ≤ U.1) (b : W.1 ≤ Z.1) (d : Derivation ℂ R ℂ)
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (TangentBasePoint.fixedFamilyFiber ℂ R Y)) :
    familyMorphismRegularDefect R f V' U W' Z h' (t.trans a) (s.trans b) d z =
      (TangentBasePoint.fixedFamilyFiber ℂ R X).left.presheaf.map
        (homOfLE ((FixedFiber.CoordinateProjection.fixedFamilyProjection R ℂ X).preimage_mono t)).op
        (familyMorphismRegularDefect R f V U W Z h a b d z) :=
  (congrArg (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv R ℂ X V')
    (DefectRestriction.familyMorphismConormalDefect_restrict R f V V' U W W' Z t s h h' a b d z)).trans
      (FixedFiber.RegularSections.fixedFiberRegularSectionEquiv_restrict R ℂ X t _)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyMorphism.RegularDefects
