import OAI.AlgebraicGeometry.Comparison.Betti.BrutalMappedExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.InverseExtension
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.OpenNatComplex
import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.FiltrationExtension

/-! # Truncated Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedPullback

noncomputable section

/-! The actual truncated algebraic pullback preserves its original inclusion and is invertible under open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (r : ℤ)

def algebraicTruncatedPullbackInt :
    ((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).obj (FiltrationExtension.algebraicTruncationComplexInt Y r) ⟶
      FiltrationExtension.algebraicTruncationComplexInt X r :=
  BrutalMappedExtension.Hodge.brutalMappedExtension (Sheaves.inverseImage f) (Sheaves.algebraicDeRhamSheafComplex Y)
    (Sheaf.CochainPullback.deRhamSheafPullback f) r

theorem algebraicTruncatedPullbackInt_inclusion :
    algebraicTruncatedPullbackInt f r ≫ FiltrationExtension.algebraicTruncationInclusionInt X r =
      ((Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)).map (FiltrationExtension.algebraicTruncationInclusionInt Y r) ≫
        OpenForms.deRhamSheafPullbackInt f := by
  let F := (Sheaves.inverseImage f).mapHomologicalComplex (.up ℤ)
  let eX := Analytic.De.algebraicSheafIntExtensionIso X
  let eY := Analytic.De.algebraicSheafIntExtensionIso Y
  let iX := HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Sheaves.algebraicDeRhamSheafComplex X) r)
    (ComplexShape.embeddingUpIntGE 0)
  let iY := HomologicalComplex.extendMap (Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (Sheaves.algebraicDeRhamSheafComplex Y) r)
    (ComplexShape.embeddingUpIntGE 0)
  let t := algebraicTruncatedPullbackInt f r
  let g := (Complex.Extension.mapExtendIso (Sheaves.inverseImage f) (ComplexShape.embeddingUpIntGE 0)
    (Sheaves.algebraicDeRhamSheafComplex Y)).hom ≫
      HomologicalComplex.extendMap (Sheaf.CochainPullback.deRhamSheafPullback f) (ComplexShape.embeddingUpIntGE 0)
  let p := OpenForms.deRhamSheafPullbackInt f
  have ht : t ≫ iX = F.map iY ≫ g :=
    BrutalMappedExtension.Hodge.brutalMappedExtension_inclusion (Sheaves.inverseImage f) (Sheaves.algebraicDeRhamSheafComplex Y)
      (Sheaf.CochainPullback.deRhamSheafPullback f) r
  have hp : F.map eY.hom ≫ g = p ≫ eX.hom := InverseExtension.algebraicInverseImage_extension_square f
  have hg : g = F.map eY.inv ≫ (p ≫ eX.hom) := (F.mapIso eY).eq_inv_comp.mpr hp
  change t ≫ (iX ≫ eX.inv) = F.map (iY ≫ eY.inv) ≫ p
  rw [F.map_comp]
  have hlast : (F.map iY ≫ F.map eY.inv ≫ (p ≫ eX.hom)) ≫ eX.inv =
      (F.map iY ≫ F.map eY.inv) ≫ p := by
    simp only [Category.assoc, eX.hom_inv_id, Category.comp_id]
  exact (Category.assoc t iX eX.inv).symm.trans
    ((congrArg (· ≫ eX.inv) ht).trans
      ((congrArg (fun z => (F.map iY ≫ z) ≫ eX.inv) hg).trans hlast))

theorem algebraicTruncatedPullbackInt_isIso [IsOpenImmersion f.left] :
    IsIso (algebraicTruncatedPullbackInt f r) := by
  have : IsIso (Sheaf.CochainPullback.deRhamSheafPullback f) := OpenNatComplex.deRhamSheafPullback_isIso_of_openImmersion f
  exact BrutalMappedExtension.Hodge.brutalMappedExtension_isIso (Sheaves.inverseImage f) (Sheaves.algebraicDeRhamSheafComplex Y)
    (Sheaf.CochainPullback.deRhamSheafPullback f) r

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.TruncatedPullback
