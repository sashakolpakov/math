import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo

/-! # Pullback Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.PullbackUnit.Intrinsic

noncomputable section

/-! The actual sheaf de Rham pullback on sections is induced by the
literal pullback of regular functions through the sheafification unit. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit.Intrinsic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R : Type u) [CommRing R]
  (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y) (U : Y.left.Opens)

def sectionMap : SectionUnit.Intrinsic.sections R Y U ⟶ SectionUnit.Intrinsic.sections R X (f.left ⁻¹ᵁ U) :=
  ((SectionUnit.Intrinsic.evaluation R Y U).mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f)

def ordinaryMap : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (SectionUnit.Intrinsic.ring R Y U) ⟶
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (SectionUnit.Intrinsic.ring R X (f.left ⁻¹ᵁ U)) :=
  OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sectionPullback f U))

theorem unit_square : SectionUnit.Intrinsic.unit R Y U ≫ sectionMap R X Y f U =
    ordinaryMap R X Y f U ≫ SectionUnit.Intrinsic.unit R X (f.left ⁻¹ᵁ U) := by
  let A := AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafificationComplexAdjunction Y
  have h : A.unit.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R Y) ≫
      ((sheafToPresheaf (Opens.grothendieckTopology Y.left) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.presheafToDirectImageSheafComplex f :=
    (A.homEquiv_unit _ _ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.sheafDirectImage f)).symm.trans
      ((A.homEquiv _ _).apply_symm_apply _)
  apply HomologicalComplex.Hom.ext
  funext n
  have hn := congrArg (fun k => (k.f n).app (op U)) h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, SectionUnit.Intrinsic.unit_f, SectionUnit.Intrinsic.unit_f]
  exact hn

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.PullbackUnit.Intrinsic
