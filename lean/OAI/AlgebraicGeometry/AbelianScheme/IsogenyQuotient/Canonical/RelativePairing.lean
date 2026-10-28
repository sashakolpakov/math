import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Torsion.SheafPairing
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierDuality

/-! # Relative Pairing -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction

noncomputable section

/-!
CartierDuality's actual character-line construction gives the native Weil and
polarization pairings over every base. The comparison retains every
test-scheme value and the original polarization map on torsion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {A : CartierDuality.PolarizedTorsion.AbelianScheme S}
  (pol : CartierDuality.PolarizedTorsion.Polarization A) (n : ℕ) (hn : 0 < n)

local instance canonicalPolarization_isMonHom :
    IsMonHom (show A.toOver ⟶ pol.dual.abelian from pol.map) := pol.preservesGroup

include pol hn in
theorem canonicalNativeTorsion_finiteLocallyFree :
    IsFinite (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom ∧
      Flat (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom ∧
      LocallyOfFinitePresentation (Torsion.Groups.Construction.nativeTorsionScheme A.toOver n).hom := by
  have : IsFinite (show A.toOver ⟶ pol.dual.abelian from pol.map).left := pol.finite
  have : IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left :=
    CartierDuality.RelativeTorsion.Construction.RelativeAbelian.finite_positive_power A.toOver pol.dual pol.map n hn
  have h := CartierDuality.TorsionGeometry.Construction.Schemes.nativeTorsion_finiteLocallyFree_of_finite_power (Grp.mk A.toOver) n
  have : IsFinite (TorsionQuotient.SubgroupFunctor.torsionScheme A.toOver n).hom := h.1
  have : Flat (TorsionQuotient.SubgroupFunctor.torsionScheme A.toOver n).hom := h.2.1
  have : LocallyOfFinitePresentation (TorsionQuotient.SubgroupFunctor.torsionScheme A.toOver n).hom := h.2.2
  have : IsIso (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv.left :=
    (Over.forget S).map_isIso (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv
  rw [← (Torsion.Groups.Construction.torsionEqualizerKernelIso A.toOver n).inv.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

def canonicalNativeWeilPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme pol.dual.abelian n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.toOver) (Grp.mk pol.dual.abelian) n
    (pol.weilPairing n hn)

theorem canonicalNativeWeilPairing_isPerfect :
    (canonicalNativeWeilPairing pol n hn).toSheafPairing.IsPerfect :=
  Torsion.SheafPairing.Construction.torsionSheafPairingToNative_isPerfect (Grp.mk A.toOver) (Grp.mk pol.dual.abelian) n
    (pol.weilPairing n hn) (pol.weilPairing_isPerfect n hn)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalNativeWeilPairing_characterLine (T : Over S)
    (x : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
    (y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme pol.dual.abelian n) :
    ULift.up ((canonicalNativeWeilPairing pol n hn).pairValue x y) =
      CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue (A.torsionSheaf n) T
        ((pol.torsionCartierIso n hn).inv.hom.app (.op T)
          ((Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk pol.dual.abelian) n).hom.hom.app (.op T) (ULift.up y)))
        ((Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x)) := by
  have hadjoint : (pol.weilPairing n hn).rightAdjoint = (pol.torsionCartierIso n hn).inv :=
    congrArg CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.leftAdjoint
      (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.flip_flip (CartierDuality.SheafEvaluation.Construction.Schemes.BilinearPairing.mk (pol.torsionCartierIso n hn).inv))
  have hv := Torsion.SheafPairing.Construction.torsionSheafPairingToNative_rightValue (Grp.mk A.toOver)
    (Grp.mk pol.dual.abelian) n (pol.weilPairing n hn) T x y
  rw [hadjoint] at hv
  exact hv

def canonicalNativePolarizationPairing :
    Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
      (B := Torsion.Groups.Construction.nativeTorsionScheme A.toOver n)
      (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) :=
  Torsion.SheafPairing.Construction.torsionSheafPairingToNative (Grp.mk A.toOver) (Grp.mk A.toOver) n
    (pol.torsionPairing n hn)

theorem canonicalNativePolarizationPairing_toSheaf :
    (canonicalNativePolarizationPairing pol n hn).toSheafPairing =
      (pol.torsionPairing n hn).restrict
        (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom
        (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom :=
  Torsion.SheafPairing.Construction.torsionSheafPairingToNative_toSheaf (Grp.mk A.toOver) (Grp.mk A.toOver) n
    (pol.torsionPairing n hn)

theorem canonicalNativePolarizationPairing_isPerfect
    (hdegree : ∀ s : S, Nat.Coprime n (pol.fiberDegree s)) :
    (canonicalNativePolarizationPairing pol n hn).toSheafPairing.IsPerfect :=
  Torsion.SheafPairing.Construction.torsionSheafPairingToNative_isPerfect (Grp.mk A.toOver) (Grp.mk A.toOver) n
    (pol.torsionPairing n hn) (pol.torsionPairing_isPerfect n hn hdegree)

theorem canonicalNativePolarizationPairing_value (T : Over S)
    (x y : T ⟶ Torsion.Groups.Construction.nativeTorsionScheme A.toOver n) :
    (canonicalNativePolarizationPairing pol n hn).pairValue x y =
      (canonicalNativeWeilPairing pol n hn).pairValue x (y ≫ Torsion.Groups.Construction.nativeTorsionMap n pol.map) := by
  let f : Grp.mk A.toOver ⟶ Grp.mk pol.dual.abelian := Grp.homMk pol.map
  have hmap := congrArg (fun e => e.hom.app (.op T) (ULift.up y))
    (Torsion.SheafComparison.Construction.kernelTorsionSheafIso_natural n f)
  change (Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk pol.dual.abelian) n).hom.hom.app (.op T)
      (ULift.up (y ≫ Torsion.Groups.Construction.nativeTorsionMap n pol.map)) =
    (pol.torsionMap n).hom.app (.op T)
      ((Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y)) at hmap
  apply ULift.up_injective
  refine (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_value (Grp.mk A.toOver) (Grp.mk A.toOver) n
    (pol.torsionPairing n hn) T x y).trans ?_
  have hv := CartierDuality.SheafEvaluation.Construction.Schemes.cartierDualSheafMap_value (pol.torsionMap n) T
    ((pol.weilPairing n hn).leftAdjoint.hom.app (.op T)
      ((Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up x)))
    ((Torsion.SheafComparison.Construction.kernelTorsionSheafIso (Grp.mk A.toOver) n).hom.hom.app (.op T) (ULift.up y))
  refine hv.trans ?_
  rw [← hmap]
  exact (Torsion.SheafPairing.Construction.torsionSheafPairingToNative_value (Grp.mk A.toOver) (Grp.mk pol.dual.abelian) n
    (pol.weilPairing n hn) T x (y ≫ Torsion.Groups.Construction.nativeTorsionMap n pol.map)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.RelativePairing.Construction
