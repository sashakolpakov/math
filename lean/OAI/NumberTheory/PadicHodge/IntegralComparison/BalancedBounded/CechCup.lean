import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.ExtCoefficientEdge

/-! # Cech Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup

noncomputable section

/-! The balanced native frame cup on the original bounded crystalline
Ext groups. The original source-dimension-shift cup is retained separately. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (hcover : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.complex (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) R F
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringPresentationResolution.augmentation (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) R F

def resolution : InjectiveResolution Y := injectiveResolution Y

def resolutionHomologyIso (i : ℕ) :
    (BoundedFrame.ResolutionCohomology.complex p k f n F).homology i ≅ ModuleCat.of R (H i) := by
  let : QuasiIso e := CoveringPresentationResolution.augmentation_quasiIso.{u + 1, u}
    (BoundedCrystalline.Site.topology f n) R F hcover
  exact Balanced.ResolutionCohomology.homologyIso R P e (resolution p k f n)
    (BoundedFrame.ResolutionAcyclicity.subsingleton p k f n F) i

def sheafHomologyIso (i : ℕ) :
    (BoundedFrame.CechCohomology.complex p k f n F).homology i ≅ ModuleCat.of R (H i) :=
  HomologicalComplex.homologyMapIso (BoundedFrame.CechCohomology.comparison p k f n F).symm i ≪≫
    resolutionHomologyIso p k f n F hcover i

def presheafHomologyIso (i : ℕ) :
    (BoundedFrame.CechPresheafCohomology.complex p k f n F).homology i ≅ ModuleCat.of R (H i) :=
  HomologicalComplex.homologyMapIso (BoundedFrame.CechPresheafCohomology.sheafIso p k f n F) i ≪≫
    sheafHomologyIso p k f n F hcover i

def cohomologyEquiv (i : ℕ) :
    (Cosimplicial.ModuleComplex.complex (BoundedCrystalline.CechCup.cochainAlgebra f n F)).homology i ≃ₗ[R] H i :=
  (HomologicalComplex.homologyMapIso (BoundedCrystalline.CechCup.comparison f n F) i).toLinearEquiv |>.trans
    ((Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n F) i).trans
        (presheafHomologyIso p k f n F hcover i).toLinearEquiv)

def cup (i j : ℕ) : H i →ₗ[R] H j →ₗ[R] H (i + j) :=
  (((Cosimplicial.ModuleCup.cohomologyCup (BoundedCrystalline.CechCup.cochainAlgebra f n F) i j).comp
    (cohomologyEquiv p k f n F hcover i).symm.toLinearMap).compl₂
      (cohomologyEquiv p k f n F hcover j).symm.toLinearMap).compr₂
        (cohomologyEquiv p k f n F hcover (i + j)).toLinearMap

theorem cohomologyEquiv_apply (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (BoundedCrystalline.CechCup.cochainAlgebra f n F)).homology i) :
    cohomologyEquiv p k f n F hcover i x =
      (presheafHomologyIso p k f n F hcover i).hom
        (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
          (BoundedFrame.CechComplex.presheafComplex f n F) i
          (HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison f n F).hom i x)) := rfl

theorem cup_comparison (i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (BoundedCrystalline.CechCup.cochainAlgebra f n F)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (BoundedCrystalline.CechCup.cochainAlgebra f n F)).homology j) :
    cup p k f n F hcover i j
      (cohomologyEquiv p k f n F hcover i x) (cohomologyEquiv p k f n F hcover j y) =
        cohomologyEquiv p k f n F hcover (i + j)
          (Cosimplicial.ModuleCup.cohomologyCup (BoundedCrystalline.CechCup.cochainAlgebra f n F) i j x y) := by
  simp only [cup, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CechCup
