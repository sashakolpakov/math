import OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerSheaf
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitTensorPower
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePowerMap
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEpi
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.TensorRestriction

/-! # Line Bundle Tensor -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleTensor

noncomputable section

/-! The Frobenius tensor comparison is an epimorphism between line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}}

def tensorPowerLineBundle (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (n : ℕ) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X where
  sheaf := TensorPowerSheaf.Construction.tensorPowerSheaf L.sheaf n
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyTrivial x
    refine ⟨U, hx, ?_⟩
    have h := ((TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf n).pullback_of_isOpenImmersion U.ι).of_sourceIso e
    exact h.unique (UnitTensorPower.Construction.unit_isTensorPower U.toScheme n)

def lineBundleFrobeniusTensorMap (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (L.pullback (Frobenius.Construction.absoluteFrobenius p hp X hX)).sheaf ⟶ (tensorPowerLineBundle L p).sheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Frobenius.Construction.absoluteFrobenius p hp X hX)).homEquiv
    L.sheaf (TensorPowerSheaf.Construction.tensorPowerSheaf L.sheaf p)).symm
      (LineBundlePowerMap.Construction.lineBundleFrobeniusToPushforward p hp hX L _ (TensorPowerSheaf.Construction.tensorPowerSheafMultilinear L.sheaf p))

theorem lineBundleFrobeniusTensorMap_homEquiv
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (P : X.Modules) (f : (tensorPowerLineBundle L p).sheaf ⟶ P) :
    LineBundlePowerMap.Construction.lineBundleFrobeniusToPushforward p hp hX L P (TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L.sheaf p P f) =
      (Scheme.Modules.pullbackPushforwardAdjunction (Frobenius.Construction.absoluteFrobenius p hp X hX)).homEquiv
        L.sheaf P (lineBundleFrobeniusTensorMap p hp hX L ≫ f) := by
  rw [← TensorPowerSheaf.Construction.tensorPowerSheafMultilinear_postcomp, LineBundlePowerMap.Construction.lineBundleFrobeniusToPushforward_postcomp]
  rw [Adjunction.homEquiv_naturality_right]
  change _ = (((Scheme.Modules.pullbackPushforwardAdjunction
    (Frobenius.Construction.absoluteFrobenius p hp X hX)).homEquiv _ _)
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (Frobenius.Construction.absoluteFrobenius p hp X hX)).homEquiv _ _).symm _)) ≫ _
  rw [Equiv.apply_symm_apply]
  rfl

instance lineBundleFrobeniusTensorMap_epi
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    Epi (lineBundleFrobeniusTensorMap p hp hX L) where
  left_cancellation f g h := by
    apply (TensorPowerSheaf.Construction.tensorPowerSheafHomEquiv L.sheaf p _).injective
    apply LineBundlePowerMap.Construction.lineBundleFrobeniusToPushforward_injective p hp hX L _
    rw [lineBundleFrobeniusTensorMap_homEquiv, lineBundleFrobeniusTensorMap_homEquiv]
    exact congrArg ((Scheme.Modules.pullbackPushforwardAdjunction
      (Frobenius.Construction.absoluteFrobenius p hp X hX)).homEquiv L.sheaf _) h

instance lineBundleFrobeniusTensorMap_isIso
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    IsIso (lineBundleFrobeniusTensorMap p hp hX L) :=
  LineBundleEpi.Construction.lineBundle_epi_isIso (L.pullback (Frobenius.Construction.absoluteFrobenius p hp X hX))
    (tensorPowerLineBundle L p) (lineBundleFrobeniusTensorMap p hp hX L)

/-- Absolute Frobenius pullback of any line bundle on any characteristic-p
scheme is canonically isomorphic to its actual p-th tensor-power sheaf. -/
def frobeniusPullbackLineBundleIso
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    (L.pullback (Frobenius.Construction.absoluteFrobenius p hp X hX)).sheaf ≅ (tensorPowerLineBundle L p).sheaf :=
  asIso (lineBundleFrobeniusTensorMap p hp hX L)

theorem frobeniusPullback_isTensorPower
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) :
    AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L.sheaf p (L.pullback (Frobenius.Construction.absoluteFrobenius p hp X hX)).sheaf :=
  (TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf p).of_targetIso
    (frobeniusPullbackLineBundleIso p hp hX L).symm

/-- Pulling the Frobenius twist of a line bundle back along relative
Frobenius gives its p-th tensor power, over an arbitrary base scheme. -/
def relativeFrobeniusPullbackLineBundleIso
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}} (hS : (p : Γ(S, ⊤)) = 0)
    (A : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Frobenius.Construction.relativeFrobenius p hp hS A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
        (CategoryTheory.Limits.pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)) L)).sheaf ≅
      (tensorPowerLineBundle L p).sheaf :=
  (Scheme.Modules.pullbackComp (Frobenius.Construction.relativeFrobenius p hp hS A).left
    (CategoryTheory.Limits.pullback.fst A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS))).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (Frobenius.Construction.relativeFrobenius_comp_fst p hp hS A)).app L.sheaf ≪≫
    frobeniusPullbackLineBundleIso p hp (Frobenius.Construction.prime_eq_zero_of_map p hS A.hom) L

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleTensor
