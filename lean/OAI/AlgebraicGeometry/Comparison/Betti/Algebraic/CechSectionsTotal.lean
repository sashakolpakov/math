import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechResolution
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveConstantSections
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalExtension

/-! # Cech Sections Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsTotal

noncomputable section

/-! Actual global sections commute with the finite diagonals of the Čech–de Rham total complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {ι : Type} (U : ι → X.left.Opens)

abbrev algebraicAdditiveGlobalSections :
    Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0} :=
  (sheafSections (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}).obj (op ⊤)

instance algebraicAdditiveGlobalSections_additive :
    (algebraicAdditiveGlobalSections X).Additive where
  map_add := by
    intro F G f g
    rfl

def algebraicCechSectionsBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{0} (.up ℕ) (.up ℕ) :=
  TotalComplexFunctor.mapBicomplex
    (C := Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0})
    (algebraicAdditiveGlobalSections X)
    (Betti.Sheaf.CechAugmentation.sheafCechBicomplex U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X))

def algebraicCechSectionsTotalInt : CochainComplex AddCommGrpCat.{0} ℤ :=
  ((algebraicCechSectionsBicomplex X U).total (.up ℕ)).extend (ComplexShape.embeddingUpIntGE 0)

def algebraicCechSectionsTotalIso :
    algebraicCechSectionsTotalInt X U ≅
      AdditiveConstantSections.Cech.additiveGlobalSectionsComplex (TopCat.of X.left) (CechResolution.algebraicCechTotalComplexInt X U) := by
  let F := algebraicAdditiveGlobalSections X
  have hF : F.Additive := algebraicAdditiveGlobalSections_additive X
  let K : HomologicalComplex₂
      (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{0}) (.up ℕ) (.up ℕ) :=
    Betti.Sheaf.CechAugmentation.sheafCechBicomplex U (AdditiveComplexExtension.algebraicAdditiveSheafComplex X)
  exact @Finite.TotalExtension.finiteTotalExtensionIso _ _ _ _ _ _ _ _ _ _ F hF K

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.CechSectionsTotal
