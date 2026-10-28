import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.GroupAmple
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.AlbaneseRationalEnd
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cohomology
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter
import OAI.ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality

/-! # Albanese Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Projective presentations and abelian-variety structures on the
literal complex Albanese groups in TateComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

def AlbaneseProjectivity.properComplexGroupVariety (A : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton A.hom
  exact {
    variety := ⟨{
      carrier := A.left
      structureMap := A.hom
      projective := AbelianModuli.ReferenceFamily.Intrinsic.ProjectiveAdapter.ProjectiveCoefficients.nativeProjectivePresentation
        (GroupAmple.properGroupProjectivePresentation A)
      smooth := inferInstance }, ArithmeticGeometry.Models.SpreadingOut.SmoothGeometricIntegrality.Construction.smooth_connected_scheme_integral A.hom⟩
    group := inferInstanceAs (GrpObj A)
    commutative := inferInstanceAs (IsCommMonObj A) }

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)

def Data.SphericalPELAlbaneseData.actualComplexAlbaneseVariety : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : Smooth D.albaneseGroup.X.hom := (CentralAction.AlbaneseExt.Construction.albaneseGroup_smooth_proper D hg).1
  have : IsProper D.albaneseGroup.X.hom := (CentralAction.AlbaneseExt.Construction.albaneseGroup_smooth_proper D hg).2
  have : GeometricallyConnected D.albaneseGroup.X.hom := D.albaneseGroup_geometricallyConnected hg
  have : Smooth D.complexAlbanese.X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
  have : IsProper D.complexAlbanese.X.hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
  have : GeometricallyConnected D.complexAlbanese.X.hom :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd D.albaneseGroup.X.hom D.complexGenericPoint))
  exact AlbaneseProjectivity.properComplexGroupVariety D.complexAlbanese.X

@[simp] theorem Data.SphericalPELAlbaneseData.actualComplexAlbaneseVariety_toOver :
    (D.actualComplexAlbaneseVariety hg).toOver = D.complexAlbanese.X := rfl

def Data.SphericalPELAlbaneseData.actualComplexComponentAlbaneseVariety (j : Fin D.componentCount) : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety := by
  have : Smooth (D.components.A j).X.hom := (hg.abelianGeometry j).1
  have : IsProper (D.components.A j).X.hom := (hg.abelianGeometry j).2.1
  have : GeometricallyConnected (D.components.A j).X.hom := (hg.abelianGeometry j).2.2
  have : Smooth (D.components.complexAbelian D.complexPoint j).X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd (D.components.A j).X.hom D.complexPoint))
  have : IsProper (D.components.complexAbelian D.complexPoint j).X.hom :=
    inferInstanceAs (IsProper (CategoryTheory.Limits.pullback.snd (D.components.A j).X.hom D.complexPoint))
  have : GeometricallyConnected (D.components.complexAbelian D.complexPoint j).X.hom :=
    inferInstanceAs (GeometricallyConnected (CategoryTheory.Limits.pullback.snd (D.components.A j).X.hom D.complexPoint))
  exact AlbaneseProjectivity.properComplexGroupVariety (D.components.complexAbelian D.complexPoint j).X

@[simp] theorem Data.SphericalPELAlbaneseData.actualComplexComponentAlbaneseVariety_toOver (j : Fin D.componentCount) :
    (D.actualComplexComponentAlbaneseVariety hg j).toOver =
      (D.components.complexAbelian D.complexPoint j).X := rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
