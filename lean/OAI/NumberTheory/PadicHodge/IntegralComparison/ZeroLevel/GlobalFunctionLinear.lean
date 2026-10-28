import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalSectionInjectivity

/-! # Global Function Linear -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctionLinear

noncomputable section

/-! The original level-zero crystalline cohomology injects linearly into the actual global section ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.AffineOpenSections OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctions

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)

theorem value_smul (w : R) (s : AffineOpenSections.Sections p k X) :
    GlobalFunctions.value p k X (w • s) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X ⊤ (WittVector.constantCoeff w.down) *
        GlobalFunctions.value p k X s := by
  symm
  apply GlobalFunctions.unique p k X
  intro U hU
  rw [map_mul, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap_naturality,
    GlobalFunctions.restriction, AffineOpenSections.value_smul]

theorem value_constants (w : R) :
    GlobalFunctions.value p k X (BoundedCrystalline.CrystallineSections.constants f 0 w) =
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X ⊤ (WittVector.constantCoeff w.down) := by
  symm
  apply GlobalFunctions.unique p k X
  intro U hU
  rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap_naturality]
  exact (BoundedCrystalline.CrystallineSections.value_constants f 0 w (AffineOpenSections.frame p k X U hU)).symm

abbrev coefficientModule : ModuleCat.{u + 1} R :=
  (BigCrystallineCohomology.largePresheaf
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k (AffineOpenSections.sectionRing k X ⊤)))).obj
      (op (LevelFrame.frame p k (AffineOpenSections.sectionRing k X ⊤)))

def sectionsMap : AffineOpenSections.Sections p k X →ₗ[R] coefficientModule p k X where
  toFun s := ULift.up (GlobalFunctions.value p k X s)
  map_add' s t := congrArg ULift.up (GlobalFunctions.value_add p k X s t)
  map_smul' w s := congrArg ULift.up (value_smul p k X w s)

def cohomologyMap : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p k)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0 0 →ₗ[R]
      coefficientModule p k X :=
  (sectionsMap p k X).comp (BoundedCrystalline.CrystallineSections.cohomologyEquiv f 0).toLinearMap

theorem sectionsMap_injective [Fintype k] [Smooth X.hom] : Function.Injective (sectionsMap p k X) := by
  intro s t h
  exact GlobalSectionInjectivity.injective p k X (congrArg ULift.down h)

theorem cohomologyMap_injective [Fintype k] [Smooth X.hom] : Function.Injective (cohomologyMap p k X) :=
  (sectionsMap_injective p k X).comp (BoundedCrystalline.CrystallineSections.cohomologyEquiv f 0).injective

theorem sectionsMap_constants (w : R) :
    sectionsMap p k X (BoundedCrystalline.CrystallineSections.constants f 0 w) =
      ULift.up (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionBaseMap k X ⊤ (WittVector.constantCoeff w.down)) :=
  congrArg ULift.up (value_constants p k X w)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctionLinear
