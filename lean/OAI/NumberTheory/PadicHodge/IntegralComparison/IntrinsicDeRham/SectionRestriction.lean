import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit

noncomputable section

/-! Restriction compatibility for the native de Rham section-unit map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (R : Type u) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {U V : X.left.Opens} (i : V ⟶ U)

@[instance_reducible]
def restrictionAlgebra : Algebra (SectionUnit.Intrinsic.ring R X U) (SectionUnit.Intrinsic.ring R X V) :=
  ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.toRingHom.toAlgebra

theorem restrictionTower : letI := restrictionAlgebra R X i
    IsScalarTower R (SectionUnit.Intrinsic.ring R X U) (SectionUnit.Intrinsic.ring R X V) := by
  let := restrictionAlgebra R X i
  exact IsScalarTower.of_algebraMap_eq (fun r =>
    (((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op).hom.commutes r).symm)

theorem restrictionEtale (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI := restrictionAlgebra R X i
    Algebra.Etale (SectionUnit.Intrinsic.ring R X U) (SectionUnit.Intrinsic.ring R X V) := by
  let := restrictionAlgebra R X i
  change (X.left.presheaf.map i.op).hom.Etale
  have h := Scheme.Hom.etale_appLE (𝟙 X.left) hU hV (show V ≤ (𝟙 X.left) ⁻¹ᵁ U by
    simpa using i.le)
  exact h

def restriction : SectionUnit.Intrinsic.sections R X U ⟶ SectionUnit.Intrinsic.sections R X V where
  f n := ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.map i.op
  comm' n m _ := ((OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).d n m).hom.naturality i.op

def nativeRestriction : OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (SectionUnit.Intrinsic.ring R X U) ⟶
    OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R (SectionUnit.Intrinsic.ring R X V) :=
  OrdinaryDeRhamFunctor.Ordinary.map ((OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras R X).map i.op)

theorem unit_restriction :
    SectionUnit.Intrinsic.unit R X U ≫ restriction R X i = nativeRestriction R X i ≫ SectionUnit.Intrinsic.unit R X V := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, SectionUnit.Intrinsic.unit_f]
  exact ((toSheafify (Opens.grothendieckTopology X.left)
    (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R X n)).naturality i.op).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.SectionRestriction.IntrinsicUnit
