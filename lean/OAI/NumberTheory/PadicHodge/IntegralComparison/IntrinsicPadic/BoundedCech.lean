import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.Augmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso

/-! # Bounded Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison

noncomputable section

/-! The exact bounded-frame section Čech total of the native global model
resolution computes the same total of the original injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom] (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X

variable (J : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "JT" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "m" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechInjective.IntrinsicPadicCechInjectiveComparison.map p X Y f hp n J

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

def frames : GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X →
    BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) (Witt.Crystalline.wittStructureMap p (ZMod p) Y) n :=
  fun i => GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp (U i).val (U i).property n

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison.frames p X Y f hp n
local notation "NN" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F

def presheafMap := ((sheafToPresheaf JT (ModuleCat.{1} Rcoeff)).mapHomologicalComplex (.up ℕ)).map m

def map := Presheaf.CechProductNaturality.totalMap.{1,0,0,1,1} NN
  (presheafMap p X Y f hp n J)

theorem intersection_quasiIso (r : ℕ)
    (t : Fin (r + 1) → GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    QuasiIso ((((evaluation (BoundedCrystalline.Site.Objects (p := p)
      (J := Ideal.span {(p : W)}) (δ := γ) w n)ᵒᵖ (ModuleCat.{1} Rcoeff)).obj
      (op (((NN).obj (op ⦋r⦌)).obj t))).mapHomologicalComplex (.up ℕ)).map
      (presheafMap p X Y f hp n J)) :=
  BoundedEvaluation.Intrinsic.quasiIso p X Y f hp n J
    (((NN).obj (op ⦋r⦌)).obj t) (t 0) (Pi.π (F ∘ t) 0)

theorem quasiIso : QuasiIso (IntrinsicComparison.map p X Y f hp n J) :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.TotalQuasiIso.CechTotalQuasiIso.quasiIso.{1,1} Rcoeff NN
    (presheafMap p X Y f hp n J) (intersection_quasiIso p X Y f hp n J)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.BoundedCech.IntrinsicComparison
