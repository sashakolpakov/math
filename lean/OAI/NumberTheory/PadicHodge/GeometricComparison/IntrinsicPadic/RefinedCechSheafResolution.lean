import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSliceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCover
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafAugmentationCoordinates

/-! # Refined Cech Sheaf Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSheafResolution.IntrinsicPadicRefinedCechSheafResolution

noncomputable section

/-! Every finite affine cover refining the original integral coordinate
cover gives a resolution of the original crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ) {ι : Type} [Finite ι] (U : ι → X.left.affineOpens)
  (index : ι → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X)
  (hU : ∀ i, (U i).val ≤ Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X (index i))
  (hcover : (⨆ i, (U i).val) = ⊤)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.diagram p X Y f hp n
local notation "η" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.cone p X Y f hp n
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance sheafCoproducts : HasCoproducts.{0}
    (IntegralComparison.BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)) (IntegralComparison.BoundedCrystalline.Site.topology w n)

include hcover in
omit [X.left.IsSeparated] [IsSeparated Y.hom] [IsProper X.hom] [Finite ι] in
theorem cover (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    IntegralComparison.CoveringObjectsSheafDetection.sieve
      (fun i => ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n) T ∈ IntegralComparison.BoundedCrystalline.Site.topology w n T := by
  apply FrameCover.IntrinsicPadicFrameCover.covering p X Y f hp n
    (fun i => (U i).val) (fun i => (U i).property) _ T
  intro x
  apply TopologicalSpace.Opens.mem_iSup.mp
  rw [hcover]
  trivial

include hU hcover in
theorem sheafified_quasiIso : QuasiIso (((S).mapHomologicalComplex (.up ℕ)).map
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)) := by
  apply Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso.quasiIso W (IntegralComparison.BoundedCrystalline.Site.topology w n)
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)
    (fun i => ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n)
    (cover p X Y f hp n U hcover)
  intro i
  exact RefinedCechSliceResolution.IntrinsicPadicRefinedCechSliceResolution.restricted_quasiIso p X Y f hp n U index hU i

def complex := ((S).mapHomologicalComplex (.up ℕ)).obj
  (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U)

def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex p X Y f hp n U :=
  (IntegralComparison.Bounded.RelativeSheafComplex.sourceIso w n).inv ≫
    ((S).mapHomologicalComplex (.up ℕ)).map
      (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)

include hU hcover in
theorem augmentation_quasiIso : QuasiIso (augmentation p X Y f hp n U) := by
  dsimp only [augmentation]
  apply (quasiIso_iff_comp_left (IntegralComparison.Bounded.RelativeSheafComplex.sourceIso w n).inv _).mpr
  exact sheafified_quasiIso p X Y f hp n U index hU hcover

def totalIso : complex p X Y f hp n U ≅ CechCone.Total.CechConeTotal.total U Q :=
  CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P

omit [IsProper X.hom] in
theorem diagram_augmentation : augmentation p X Y f hp n U ≫ (totalIso p X Y f hp n U).hom =
    CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O)
      (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n) :=
  (CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.augmentation S U P
    (IntegralComparison.Bounded.RelativeSheafComplex.structureIso w n) η).trans
      (congrArg (fun η' => CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O) η')
        (CechSheafAugmentationCoordinates.IntrinsicPadicCechSheafAugmentationCoordinates.cone_eq p X Y f hp n))

include hU hcover in
theorem diagram_quasiIso : QuasiIso
    (CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O)
      (PadicResolutionDiagram.IntrinsicPadicResolutionDiagram.augmentation p X Y f hp n)) := by
  rw [← diagram_augmentation p X Y f hp n U]
  exact (quasiIso_iff_comp_right _ (totalIso p X Y f hp n U).hom).mpr
    (augmentation_quasiIso p X Y f hp n U index hU hcover)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RefinedCechSheafResolution.IntrinsicPadicRefinedCechSheafResolution
