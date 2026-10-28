import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveLevelMapCoordinates

/-! # Integral Presheaf Level Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData

noncomputable section

/-! Explicit presheaf complexes and maps shared by the native integral
comparison and its original level-transition square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def source (q : ℕ) : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X q)

def target (q : ℕ) : CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ :=
  ((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f q).mapHomologicalComplex (.up ℕ)).obj
    (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution w q I).cocomplex

def comparison (q : ℕ) : source p X q ⟶ target p X Y f I q :=
  IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp q (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution w q I)

def sourceMap (n m : ℕ) (hnm : n ≤ m) : source p X m ⟶ source p X n :=
  IntegralSourceAssemblyLevel.IntrinsicPadicIntegralSourceAssemblyLevel.map p X n m hnm

def targetMap (n m : ℕ) (hnm : n ≤ m) : target p X Y f I m ⟶ target p X Y f I n :=
  InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates.sectionsMap p X Y f n m hnm I

def homotopy (n m : ℕ) (hnm : n ≤ m) : Homotopy
    (comparison p X Y f hp I m ≫ targetMap p X Y f I n m hnm)
    (sourceMap p X n m hnm ≫ comparison p X Y f hp I n) :=
  (Homotopy.ofEq ((congrArg (fun q => comparison p X Y f hp I m ≫ q)
    (InjectiveLevelMapCoordinates.IntrinsicPadicInjectiveLevelMapCoordinates.map_eq p X Y f n m hnm I)).symm)).trans
      (IntegralInjectiveLevelHomotopy.IntrinsicPadicIntegralInjectiveLevelHomotopy.homotopy p X Y f hp n m hnm I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData
