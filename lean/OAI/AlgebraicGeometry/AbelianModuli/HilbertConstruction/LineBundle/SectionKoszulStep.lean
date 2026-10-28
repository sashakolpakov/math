import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionTensor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MappingConeContractions

/-! # Section Koszul Step -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulStep

noncomputable section

/-! The mapping cone of actual tensoring by a line-bundle section contracts after every pullback on which that section is a frame. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

local instance e33KoszulStepTensorAdditive {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) :
    (TensorEquivalence.lineBundleTensorEquivalence L).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

local instance e33KoszulStepPullbackAdditive {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (Scheme.Modules.pullback f)
  exact CategoryTheory.Functor.additive_of_preservesBinaryBiproducts _

def lineBundleSectionComplexMap {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (K : CochainComplex X.Modules ℤ) :
    K ⟶ (((TensorEquivalence.lineBundleTensorEquivalence L).functor.mapHomologicalComplex (.up ℤ)).obj K) where
  f n := (SectionTensor.lineBundleSectionTensor L s).app (K.X n)
  comm' i j _ := ((SectionTensor.lineBundleSectionTensor L s).naturality (K.d i j)).symm

theorem lineBundleSectionComplexMap_isIso {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) [IsIso s] (K : CochainComplex X.Modules ℤ) :
    IsIso (lineBundleSectionComplexMap L s K) := by
  have (n : ℤ) : IsIso ((lineBundleSectionComplexMap L s K).f n) :=
    SectionTensor.lineBundleSectionTensorMap_isIso L s (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

def lineBundleSectionKoszulStep {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (K : CochainComplex X.Modules ℤ) :
    CochainComplex X.Modules ℤ := CochainComplex.mappingCone (lineBundleSectionComplexMap L s K)

theorem lineBundleSectionKoszulStep_isZero_X_iff {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (K : CochainComplex X.Modules ℤ) (i : ℤ) :
    IsZero ((lineBundleSectionKoszulStep L s K).X i) ↔
      IsZero (K.X (i + 1)) ∧ IsZero ((TensorEquivalence.lineBundleTensorEquivalence L).functor.obj (K.X i)) :=
  CochainComplex.mappingCone.isZero_X_iff _ i

theorem lineBundleSectionComplexMap_pullback_isIso {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (f : Y ⟶ X)
    [IsIso ((Scheme.Modules.pullback f).map s)] (K : CochainComplex X.Modules ℤ) :
    IsIso (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).map
      (lineBundleSectionComplexMap L s K)) := by
  have (n : ℤ) : IsIso ((((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).map
      (lineBundleSectionComplexMap L s K)).f n) :=
    SectionTensor.lineBundleSectionTensorMap_pullback_isIso L s f (K.X n)
  exact HomologicalComplex.Hom.isIso_of_components _

def lineBundleSectionKoszulStep_pullback_contractible {X Y : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (f : Y ⟶ X)
    [IsIso ((Scheme.Modules.pullback f).map s)] (K : CochainComplex X.Modules ℤ) :
    Homotopy (𝟙 (((Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)).obj
      (lineBundleSectionKoszulStep L s K))) 0 := by
  let F := Scheme.Modules.pullback f
  change Homotopy (𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj
    (CochainComplex.mappingCone (lineBundleSectionComplexMap L s K)))) 0
  let q := (F.mapHomologicalComplex (.up ℤ)).map (lineBundleSectionComplexMap L s K)
  have : IsIso q := lineBundleSectionComplexMap_pullback_isIso L s f K
  let e : (F.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mappingCone (lineBundleSectionComplexMap L s K)) ≅ CochainComplex.mappingCone q :=
    CochainComplex.mappingCone.mapHomologicalComplexIso (lineBundleSectionComplexMap L s K) F
  exact (MappingConeContractions.cochainContractible_of_iso e ⟨MappingConeContractions.mappingConeHomotopyToZeroOfIso q⟩).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionKoszulStep
