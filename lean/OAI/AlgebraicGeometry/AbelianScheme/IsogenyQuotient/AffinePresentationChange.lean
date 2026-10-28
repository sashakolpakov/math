import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ConstantConormalNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections

/-! # Affine Presentation Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePresentationChange.Construction

noncomputable section

/-! Two actual affine presentations of the same group open determine
their coordinate change. Its etaleness, ambient square, section formula,
and constant-conormal logarithm formula are derived from the open maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable (G : Over Foundations.Scheme.ProjectiveSpace.complexBase) (B D : CommAlgCat ℂ)
    (i : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B ⟶ G) (j : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ G)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (h : j.left.opensRange = i.left.opensRange)

/-- The coordinate change is the unique isomorphism of the original
open immersions, with its base compatibility derived from their maps. -/
def sameOpenAffinePresentationMap : AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D ⟶ AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B := by
  let e := IsOpenImmersion.isoOfRangeEq j.left i.left (congrArg SetLike.coe h)
  refine Over.homMk e.hom ?_
  calc
    e.hom ≫ (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ B).hom = e.hom ≫ (i.left ≫ G.hom) :=
      congrArg (fun f => e.hom ≫ f) i.w.symm
    _ = (e.hom ≫ i.left) ≫ G.hom := (Category.assoc _ _ _).symm
    _ = j.left ≫ G.hom := congrArg (fun f => f ≫ G.hom)
      (IsOpenImmersion.isoOfRangeEq_hom_fac j.left i.left (congrArg SetLike.coe h))
    _ = (AbelianModuli.ReferenceFamily.EtaleSplittingAt.EtaleSplitting.affineOver ℂ D).hom := j.w

instance sameOpenAffinePresentationMap_isIso : IsIso (sameOpenAffinePresentationMap G B D i j h).left := by
  change IsIso (IsOpenImmersion.isoOfRangeEq j.left i.left (congrArg SetLike.coe h)).hom
  infer_instance

theorem sameOpenAffinePresentationMap_square :
    sameOpenAffinePresentationMap G B D i j h ≫ i = j := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.isoOfRangeEq_hom_fac j.left i.left (congrArg SetLike.coe h)

def sameOpenAffineCoordinateMap : B →ₐ[ℂ] D :=
  AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverMorphismAlgebra ℂ D B (sameOpenAffinePresentationMap G B D i j h)

theorem sameOpenAffineCoordinateMap_square :
    AbelianModuli.ReferenceFamily.Affine.AlgebraAutomorphismNaturality.affineOverAlgHom ℂ B D (sameOpenAffineCoordinateMap G B D i j h) ≫ i = j := by
  rw [sameOpenAffineCoordinateMap, AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_recovery]
  exact sameOpenAffinePresentationMap_square G B D i j h

theorem sameOpenAffineCoordinateMap_etale :
    (sameOpenAffineCoordinateMap G B D i j h).toRingHom.Etale := by
  have he : Etale (Spec.map (CommRingCat.ofHom
      (sameOpenAffineCoordinateMap G B D i j h).toRingHom)) := by
    rw [sameOpenAffineCoordinateMap, AbelianModuli.ReferenceFamily.Affine.OverMorphismAlgebra.affineOverMorphismAlgebra_spec]
    exact inferInstanceAs (Etale (IsOpenImmersion.isoOfRangeEq j.left i.left
      (congrArg SetLike.coe h)).hom)
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (sameOpenAffineCoordinateMap G B D i j h).toRingHom)).mp he

theorem sameOpenAffineCoordinateMap_sections (a : B) :
    AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ D G j (sameOpenAffineCoordinateMap G B D i j h a) =
      G.left.presheaf.map (homOfLE h.le).op (AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv ℂ B G i a) :=
  AbelianModuli.ReferenceFamily.Affine.PresentationRegularSections.affinePresentationRegularSectionEquiv_natural ℂ B G i D j
    (sameOpenAffineCoordinateMap G B D i j h)
    (sameOpenAffineCoordinateMap_square G B D i j h) h.le a

variable [IsIntegral G.left] [Smooth G.hom] [GrpObj G]

/-- No derivation or coordinate compatibility is assumed: the original
open maps supply the etale coordinate change and its conormal square. -/
theorem sameOpenAffineCoordinateMap_unitLog
    (l : AbelianModuli.ReferenceFamily.Constructed.IdentityConormal.constructedIdentityConormal ℂ G →ₗ[ℂ] ℂ) (u : Bˣ) :
    AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G D j).symm (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector D l))
      (Units.map (sameOpenAffineCoordinateMap G B D i j h).toMonoidHom u) =
      sameOpenAffineCoordinateMap G B D i j h
        (AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms.coefficientUnitLog ((AbelianModuli.ReferenceFamily.Affine.PresentationConormalLinearity.affinePresentationConormalLinearEquiv G B i).symm
          (AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates.coefficientCovector B l)) u) :=
  AbelianModuli.ReferenceFamily.Affine.ConstantConormalNaturality.affineConstantConormalUnitLog_natural G B i D j (sameOpenAffineCoordinateMap G B D i j h)
    (sameOpenAffineCoordinateMap_etale G B D i j h)
    (sameOpenAffineCoordinateMap_square G B D i j h) l u

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.AffinePresentationChange.Construction
