import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCover

/-! # Cech Sheaf Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution

noncomputable section

/-! A canonical Čech resolution of the original bounded crystalline
structure sheaf from the actual finite integral étale coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of k))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))

local notation "W" => WittVector p k
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSliceResolution.opens p k n X
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem cover (T : BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    CoveringObjectsSheafDetection.sieve
      (fun i => Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property) T ∈
        BoundedCrystalline.Site.topology w n T := by
  exact FrameCover.covering p k n X Y f hp
    (fun i => (U i).val) (fun i => (U i).property)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.covers (Truncated.Witt.Ring p k n) X) T

theorem sheafified_quasiIso : QuasiIso (((S).mapHomologicalComplex (.up ℕ)).map
    (CechPresheaf.augmentation p k n X Y f hp U)) := by
  apply GeometricComparison.Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso.quasiIso W (BoundedCrystalline.Site.topology w n)
    (CechPresheaf.augmentation p k n X Y f hp U)
    (fun i => Truncated.AffineModelFrame.frame p k n X Y f hp (U i).val (U i).property)
    (cover p k n X Y f hp)
  intro i
  exact CechSliceResolution.restricted_quasiIso p k n X Y f hp i

def complex := ((S).mapHomologicalComplex (.up ℕ)).obj
  (CechPresheaf.total p k n X Y f hp U)

def augmentation :
    (CochainComplex.single₀ _).obj
      (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) ⟶
    complex p k n X Y f hp :=
  (Bounded.RelativeSheafComplex.sourceIso w n).inv ≫
    ((S).mapHomologicalComplex (.up ℕ)).map
      (CechPresheaf.augmentation p k n X Y f hp U)

theorem augmentation_quasiIso : QuasiIso (augmentation p k n X Y f hp) := by
  dsimp only [augmentation]
  apply (quasiIso_iff_comp_left (Bounded.RelativeSheafComplex.sourceIso w n).inv _).mpr
  exact sheafified_quasiIso p k n X Y f hp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechSheafResolution
