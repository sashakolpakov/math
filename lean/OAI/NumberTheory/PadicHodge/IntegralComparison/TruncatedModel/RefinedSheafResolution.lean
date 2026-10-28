import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSliceResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafAugmentationCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso

/-! # Refined Sheaf Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSheafResolution

noncomputable section

/-! Every finite affine cover refining the actual model coordinate cover gives a resolution of the original bounded crystalline structure sheaf. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  {ι : Type} [Finite ι] (U : ι → X.left.affineOpens)
  (index : ι → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index (Truncated.Witt.Ring p k n) X)
  (hU : ∀ i, (U i).val ≤ (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens (Truncated.Witt.Ring p k n) X (index i)).val)

variable (hcover : (⨆ i, (U i).val) = ⊤)
local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.diagram p k n X Y f hp
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.ResolutionDiagram.diagram p k n X Y f hp
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechPresheaf.cone p k n X Y f hp
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance sheafCoproducts : HasCoproducts.{0}
    (BoundedCrystalline.Site.ModuleSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :=
  GeometricComparison.Module.SheafCoproducts.ModuleSheafCoproducts.hasCoproducts (Crystalline.ExactRestriction.Coeff (B := W))
    (BoundedCrystalline.Site.topology w n)

include hcover in
omit [X.left.IsSeparated] [IsSeparated Y.hom] [IsProper X.hom] [Finite ι] in
theorem cover (T : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    CoveringObjectsSheafDetection.sieve
      (fun i => Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property) T ∈
      BoundedCrystalline.Site.topology w n T := by
  exact FrameCover.covering p k n X Y f hp
    (fun i => (U i).val) (fun i => (U i).property)
    (fun x => by
      have hx : x ∈ ⨆ i, (U i).val := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩) T

include hU hcover in
theorem sheafified_quasiIso : QuasiIso (((S).mapHomologicalComplex (.up ℕ)).map
    (CechPresheaf.augmentation p k n X Y f hp U)) := by
  apply GeometricComparison.Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso.quasiIso W (BoundedCrystalline.Site.topology w n)
    (CechPresheaf.augmentation p k n X Y f hp U)
    (fun i => Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property)
    (cover p k n X Y f hp U hcover)
  intro i
  exact RefinedSliceResolution.restricted_quasiIso p k n X Y f hp U index hU i

def complex := ((S).mapHomologicalComplex (.up ℕ)).obj
  (CechPresheaf.total p k n X Y f hp U)
def augmentation : (CochainComplex.single₀ _).obj O ⟶ complex p k n X Y f hp U :=
  (Bounded.RelativeSheafComplex.sourceIso w n).inv ≫
    ((S).mapHomologicalComplex (.up ℕ)).map (CechPresheaf.augmentation p k n X Y f hp U)
include hU hcover in
theorem augmentation_quasiIso : QuasiIso (augmentation p k n X Y f hp U) := by
  dsimp only [augmentation]
  apply (quasiIso_iff_comp_left (Bounded.RelativeSheafComplex.sourceIso w n).inv _).mpr
  exact sheafified_quasiIso p k n X Y f hp U index hU hcover

def totalIso : complex p k n X Y f hp U ≅ GeometricComparison.CechCone.Total.CechConeTotal.total U Q :=
  GeometricComparison.CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P

omit [IsProper X.hom] in
theorem diagram_augmentation : augmentation p k n X Y f hp U ≫ (totalIso p k n X Y f hp U).hom =
    GeometricComparison.CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O)
      (ResolutionDiagram.augmentation p k n X Y f hp) :=
  (GeometricComparison.CechCone.TotalTransportAugmentation.CechConeTotalTransportAugmentation.augmentation S U P
    (Bounded.RelativeSheafComplex.structureIso w n) η).trans
      (congrArg (fun η' => GeometricComparison.CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O) η')
        (CechSheafAugmentationCoordinates.cone_eq p k n X Y f hp))

include hU hcover in
theorem diagram_quasiIso : QuasiIso
    (GeometricComparison.CechCone.Total.CechConeTotal.augmentation U Q ((CochainComplex.single₀ _).obj O)
      (ResolutionDiagram.augmentation p k n X Y f hp)) := by
  rw [← diagram_augmentation p k n X Y f hp U]
  exact (quasiIso_iff_comp_right _ (totalIso p k n X Y f hp U).hom).mpr
    (augmentation_quasiIso p k n X Y f hp U index hU hcover)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.RefinedSheafResolution
