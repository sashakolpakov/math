import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechOpenEquality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.IncomingMap

/-! # Section Family Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionFamilyCoordinates.Family

noncomputable section

/-! The incoming section identification for equal families is the
same transport used by the supported comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C]
  (F G : C →o Y.Opens) (h : F = G)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

theorem hom :
    ((NatIso.mapHomologicalComplex
      (BoundedOpen.IncomingMap.familyIso fY n F G h) (.up ℕ)).app I.cocomplex).hom =
      eqToHom (congrArg
        (fun T => Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
          R Y.carrier T.toFunctor K) h) := by
  subst G
  rfl

theorem inv :
    ((NatIso.mapHomologicalComplex
      (BoundedOpen.IncomingMap.familyIso fY n F G h) (.up ℕ)).app I.cocomplex).inv =
      eqToHom (congrArg
        (fun T => Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
          R Y.carrier T.toFunctor K) h.symm) := by
  subst G
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.SectionFamilyCoordinates.Family
