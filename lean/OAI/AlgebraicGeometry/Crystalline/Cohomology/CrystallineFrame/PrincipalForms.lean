import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.ModuleLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.CechAugmentation

/-! # Principal Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms

noncomputable section

/-!
# Native frame forms as sections on principal opens

For a fixed actual crystalline object, every term of its frame resolution
is a module over its ambient ring. The native restriction to a principal
open is identified with sections of that module's associated sheaf by
the uniqueness of module localization.
-/

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ)

local notation "W" => WittVector p k
local notation "QR" => Q.thickening.ring
local notation "GR" => DividedPowerAlgebra QR (σ →₀ QR)

def module : ModuleCat.{u} QR := ModuleCat.of QR (Koszul.Tensor.KoszulTensor.Term W σ GR n)

def associatedSheaf : TopCat.Sheaf (ModuleCat.{u} QR) (Spec (CommRingCat.of QR)) :=
  modulesSpecToSheaf.obj (tilde (R := CommRingCat.of QR) (module p k B σ Q n))

variable (s : Q.thickening.ring)

local notation "S" => Localization.Away s
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k
  (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) Q s

def sectionsEquiv : Koszul.Tensor.KoszulTensor.Term W σ GS n ≃ₗ[QR]
    (associatedSheaf p k B σ Q n).obj.obj (op (Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR s)) := by
  let f : (module p k B σ Q n) →ₗ[QR] Koszul.Tensor.KoszulTensor.Term W σ GS n :=
    ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q s n
  have hf : IsLocalizedModule (Submonoid.powers s) f :=
    ModuleLocalization.CrystallineFrameModuleLocalization.termMap_isLocalizedModule p k B σ a Q s n
  have hg : IsLocalizedModule.Away s
      (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n) (PrimeSpectrum.basicOpen s)).hom :=
    inferInstance
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers s) f
    (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n) (PrimeSpectrum.basicOpen s)).hom
  exact e

theorem sectionsEquiv_termMap (x : Koszul.Tensor.KoszulTensor.Term W σ GR n) :
    sectionsEquiv p k B σ a Q n s (ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q s n x) =
      (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n)
        (Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR s)).hom x :=
  by
    have hg : IsLocalizedModule.Away s
        (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n) (PrimeSpectrum.basicOpen s)).hom :=
      inferInstance
    let f : (module p k B σ Q n) →ₗ[QR] Koszul.Tensor.KoszulTensor.Term W σ GS n :=
      ModuleLocalization.CrystallineFrameModuleLocalization.termMap p k B σ a Q s n
    have hf : IsLocalizedModule (Submonoid.powers s) f :=
      ModuleLocalization.CrystallineFrameModuleLocalization.termMap_isLocalizedModule p k B σ a Q s n
    have he := IsLocalizedModule.linearEquiv_apply (Submonoid.powers s) f
      (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n) (PrimeSpectrum.basicOpen s)).hom x
    exact he

theorem native_transition [Fintype σ] (x : Koszul.Tensor.KoszulTensor.Term W σ GR n) :
    sectionsEquiv p k B σ a Q n s
      ((((Koszul.Functor.KoszulFunctor.functor W σ (Operators.CrystallineFrameOperators.functions p k B σ a)
        (Operators.CrystallineFrameOperators.derivative p k B σ a)
        (Resolution.CrystallineFrameResolution.commute p k B σ a)).map (q).op).f n).hom x) =
      (tilde.toOpen (R := CommRingCat.of QR) (module p k B σ Q n)
        (Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR s)).hom x := by
  exact (congrArg (sectionsEquiv p k B σ a Q n s)
    (LinearMap.congr_fun (ModuleLocalization.CrystallineFrameModuleLocalization.termMap_native p k B σ a Q s n) x)).trans
      (sectionsEquiv_termMap p k B σ a Q n s x)

theorem associatedCech_quasiIso {ι : Type u} [Finite ι] (t : ι → Q.thickening.ring)
    (ht : Ideal.span (Set.range t) = ⊤) :
    QuasiIso (Cech.AugmentedSections.CechAugmentedSections.augmentation QR (Spec (CommRingCat.of QR))
      (fun i => Affine.IntersectionLocalization.AffineIntersectionLocalization.principal QR (t i))
      (associatedSheaf p k B σ Q n).obj ⊤) :=
  Affine.CechAugmentation.AffineCechAugmentation.tilde_quasiIso QR t (module p k B σ Q n) ht

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalForms.CrystallineFramePrincipalForms
