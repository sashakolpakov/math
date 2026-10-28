import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CoveringSheafQuasiIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameCover

/-! # Cech Sheaf Resolution -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution

noncomputable section

/-! A canonical Čech resolution of the original bounded crystalline
structure sheaf from the actual finite integral étale coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.sheafification (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem cover (T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) :
    IntegralComparison.CoveringObjectsSheafDetection.sieve
      (fun i => ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n) T ∈
        IntegralComparison.BoundedCrystalline.Site.topology w n T := by
  apply FrameCover.IntrinsicPadicFrameCover.covering p X Y f hp n
    (fun i => (U i).val) (fun i => (U i).property) _ T
  intro x
  apply TopologicalSpace.Opens.mem_iSup.mp
  change x ∈ ⨆ i, Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X i
  rw [Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.cover]
  trivial

theorem sheafified_quasiIso : QuasiIso (((S).mapHomologicalComplex (.up ℕ)).map
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)) := by
  apply Bounded.CoveringSheafQuasiIso.BoundedCoveringSheafQuasiIso.quasiIso W (IntegralComparison.BoundedCrystalline.Site.topology w n)
    (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)
    (fun i => ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n)
    (cover p X Y f hp n)
  intro i
  exact CechSliceResolution.IntrinsicPadicCechSliceResolution.restricted_quasiIso p X Y f hp n i

def complex := ((S).mapHomologicalComplex (.up ℕ)).obj
  (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U)

def augmentation :
    (CochainComplex.single₀ _).obj
      (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) ⟶
    complex p X Y f hp n :=
  (IntegralComparison.Bounded.RelativeSheafComplex.sourceIso w n).inv ≫
    ((S).mapHomologicalComplex (.up ℕ)).map
      (CechPresheafResolution.IntrinsicPadicCechPresheafResolution.augmentation p X Y f hp n U)

theorem augmentation_quasiIso : QuasiIso (augmentation p X Y f hp n) := by
  dsimp only [augmentation]
  apply (quasiIso_iff_comp_left (IntegralComparison.Bounded.RelativeSheafComplex.sourceIso w n).inv _).mpr
  exact sheafified_quasiIso p X Y f hp n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution
