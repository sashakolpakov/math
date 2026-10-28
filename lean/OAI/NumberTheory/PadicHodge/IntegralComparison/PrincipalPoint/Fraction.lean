import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue

/-! # Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction

noncomputable section

/-! The actual point-parameter principal family carries the mixed
Koszul fraction. Its residue is the original closed-scheme pullback
of the reciprocal-product coefficient, with its exact orientation. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ClosedKoszulResidue
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U) {c m : ℕ} (s : Fin c → Γ(Y, U))
  (hs : Koszul.OrientedTopCohomology.ideal Γ(Y, U) s = f.ker.ideal ⟨U, hU⟩)
  (t : Fin m → Γ(Y, U))

def family : ULift.{u} (Fin m) → Principal.SectionPresheaf.Index U := fun i => ⟨t i.down⟩

theorem units (i : ULift.{u} (Fin m)) :
    IsUnit (algebraMap Γ(Y, U) ((Principal.SectionPresheaf.rings U hU).obj (op (Fraction.family U t i))) (t i.down)) :=
  AffinePrincipal.Diagram.restricted_function_isUnit Y U hU (Fraction.family U t i)

abbrev map := KoszulPartial.ResidueTotal.map Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
  (Fraction.family U t) s t (units U hU t) (Principal.ClosedKoszulResidue.target f U hU)
  (Principal.ClosedKoszulResidue.pullback f U hU s hs) (Principal.ClosedKoszulResidue.annihilated f U hU s hs)

theorem coefficient (a : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m)
    (φ : Module.Dual Γ(Y, U)
      (⋀[Γ(Y, U)]^(c + m) (KoszulPartial.Fractions.ambient Γ(Y, U) (c := c) (m := m)))) :
    ((map f U hU s hs t).f (c + m) ≫
      (AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat (AugmentedOrdered.CechFunctor.bicomplex (family U t)
        (KoszulPartial.ResidueTotal.residueComplex Γ(Y, U) (c := c) (Principal.ClosedKoszulResidue.target f U hU)))) c m (c + m) ≫
      Pi.π (fun b : AugmentedOrdered.Cech.Index (ULift.{u} (Fin m)) m =>
        ((KoszulPartial.ResidueTotal.residueComplex Γ(Y, U) (c := c) (Principal.ClosedKoszulResidue.target f U hU)).X c).obj
          (op ((AugmentedOrdered.Cech.formal (Fraction.family U t) m).obj b))) a ≫
      (singleObjXSelf (.up ℕ) c (Principal.ClosedKoszulResidue.target f U hU)).hom.app (op ((AugmentedOrdered.Cech.formal (Fraction.family U t) m).obj a)))
        (show (KoszulPartial.Components.source Γ(Y, U) s t).X (c + m) from φ) =
      f.app (Principal.SectionPresheaf.openSubset U ((AugmentedOrdered.Cech.formal (Fraction.family U t) m).obj a))
        (KoszulPartial.Fractions.reciprocal Γ(Y, U) (Principal.SectionPresheaf.rings U hU) (Fraction.family U t) t (units U hU t) a *
          algebraMap Γ(Y, U) ((Principal.SectionPresheaf.rings U hU).obj (op ((AugmentedOrdered.Cech.formal (Fraction.family U t) m).obj a)))
            (φ (TopExteriorCoordinates.generator
              (KoszulPartial.TopResidue.basis Γ(Y, U) (c := c) (m := m))))) := by
  exact (KoszulPartial.ResidueTotal.coefficient Γ(Y, U) (Principal.SectionPresheaf.rings U hU)
    (Fraction.family U t) s t (units U hU t) (Principal.ClosedKoszulResidue.target f U hU)
    (Principal.ClosedKoszulResidue.pullback f U hU s hs) (Principal.ClosedKoszulResidue.annihilated f U hU s hs) a φ).trans
      (Principal.ClosedKoszulResidue.pullback_apply f U hU s hs _ _)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalPoint.Fraction
