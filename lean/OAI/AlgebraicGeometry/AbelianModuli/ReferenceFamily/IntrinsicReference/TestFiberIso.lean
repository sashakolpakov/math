import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ComplexUniversal
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Points
import OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm

/-! # Test Fiber Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! A test-family point equal to an original reference moduli point
has an actual group isomorphism from that reference algebraic model to
its native fiber. This uses only the exact fine moduli property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm

attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.referencePoint

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ)
    (a : P.domain) (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    (hy : y ≫ f = M.referencePoint hM κ hP hκ a)

include hy in
theorem Models.FinePELModel.complexTestFamily_reference_iso : Nonempty
    (PEL.Objects.PELIso (P.referencePELObject hP a iota κ hκ N)
      ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y))) := by
  apply (PEL.Objects.PELObject.classOf_eq_iff _ _).mp
  calc
    (P.referencePELObject hP a iota κ hκ N).classOf =
        (M.universal.pullback (M.complexPointBaseEquiv κ (M.referencePoint hM κ hP hκ a))).classOf :=
      (M.referencePoint_class hM κ hP hκ a).symm
    _ = (M.universal.pullback (M.complexPointBaseEquiv κ (y ≫ f))).classOf :=
      congrArg (fun p => (M.universal.pullback (M.complexPointBaseEquiv κ p)).classOf) hy.symm
    _ = ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)).classOf :=
      (M.complexTestFamily_point_class κ f y).symm

def Models.FinePELModel.referenceTestFiberIso :
    PEL.Objects.PELIso (P.referencePELObject hP a iota κ hκ N)
      ((M.complexTestFamily κ f).pullback (Intrinsic.ComplexUniversal.complexPointRestriction κ y)) :=
  Classical.choice (M.complexTestFamily_reference_iso hM κ hP hκ f a y hy)

attribute [local irreducible] Models.FinePELModel.referenceTestFiberIso

def Models.FinePELModel.nativeReferenceTestFiberIso :
    (Reference.AlgebraicModel.referenceAlgebraicModel (Reference.Fiber.referenceAnalyticFiber P hP a) hP).abelian.toOver ≅
      (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver :=
  (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelian ≪≫
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).comparison

instance Models.FinePELModel.nativeReferenceTestFiberIso_group :
    IsMonHom (M.nativeReferenceTestFiberIso hM κ hP hκ f a y hy).hom := by
  let : GrpObj (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.toOver :=
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.group
  change IsMonHom ((M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelian.hom ≫
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).comparison.hom)
  exact @instIsMonHomComp (Over Foundations.Scheme.ProjectiveSpace.complexBase) _ _ _ _ _
    (P.referencePELObject hP a iota κ hκ N).polarized.abelian.group.toMonObj
    ((M.complexTestFamily κ f).polarized.abelian.pullback y.left).group.toMonObj
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).variety.group.toMonObj
    (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelian.hom
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).comparison.hom
    (M.referenceTestFiberIso hM κ hP hκ f a y hy).polarized.abelianGroup
    (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized y).comparison_group

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
