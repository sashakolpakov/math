import OAI.NumberTheory.PadicHodge.IntegralComparison.SingleCechLocalizationTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.OpenLocalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor

/-! # Open Fixed Class -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenFixedClass

noncomputable section

/-! On the original nested pushforward principal diagram, restriction
to D(z) detects equality of z-fixed supported single-degree classes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction
variable {Y X Z : Scheme.{u}} (f : Y ⟶ X) (i : X ⟶ Z)
  (U : Z.Opens) (hU : IsAffineOpen U) (N : Y.Modules)

abbrev source := Principal.SectionPresheaf.modules U hU (OpenRestriction.image f i N)

def coefficientIso :
    Principal.ClosedScalars.modules (f ≫ i) U hU N ⋙
        ModuleCat.restrictScalars ((f ≫ i).app U).hom ≅ source f i U hU N :=
  Principal.ClosedScalars.restrictionIso (f ≫ i) U hU N ≪≫
    (Principal.ModuleFunctor.functor U hU).mapIso (((Scheme.Modules.pushforwardComp f i).app N).symm)

variable (z : Γ(Y, (f ≫ i) ⁻¹ᵁ U))

def scalar : source f i U hU N ⟶ source f i U hU N :=
  (coefficientIso f i U hU N).inv ≫
    Functor.whiskerRight (z • 𝟙 (Principal.ClosedScalars.modules (f ≫ i) U hU N))
      (ModuleCat.restrictScalars ((f ≫ i).app U).hom) ≫
        (coefficientIso f i U hU N).hom

theorem scalar_square :
    Functor.whiskerRight (z • 𝟙 (Principal.ClosedScalars.modules (f ≫ i) U hU N))
        (ModuleCat.restrictScalars ((f ≫ i).app U).hom) ≫ (coefficientIso f i U hU N).hom =
      (coefficientIso f i U hU N).hom ≫ scalar f i U hU N z := by
  rw [scalar, Iso.hom_inv_id_assoc]

theorem scalar_app (r : Principal.SectionPresheaf.Index U) (x : Γ(N, f ⁻¹ᵁ (i ⁻¹ᵁ Principal.SectionPresheaf.openSubset U r))) :
    (scalar f i U hU N z).app (op r) x =
      Y.presheaf.map (Principal.ClosedScalars.pullbackInclusion (f ≫ i) U r).op z •
        (show Γ(N, Principal.ClosedScalars.pullbackOpen (f ≫ i) U r) from x) := rfl

theorem map_square :
    Functor.whiskerRight (Principal.OpenLocalization.map (f ≫ i) U hU N z)
        (ModuleCat.restrictScalars ((f ≫ i).app U).hom) ≫
      (coefficientIso f i U hU (OpenRestriction.extension (Y.basicOpen z) N)).hom =
    (coefficientIso f i U hU N).hom ≫ OpenRestriction.map f i U hU (Y.basicOpen z) N := by
  apply NatTrans.ext
  funext r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

variable [IsAffineHom (f ≫ i)] [N.IsQuasicoherent]
  {ι : Type u} [LinearOrder ι] [Finite ι] (W : ι → Principal.SectionPresheaf.Index U) (c n : ℕ)

local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenRestriction.supportedFunctor U W c (n+c)

theorem eq_of_map_eq (x y : (S).obj (source f i U hU N))
    (hx : (S).map (scalar f i U hU N z) x = x)
    (hy : (S).map (scalar f i U hU N z) y = y)
    (h : OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N W c (n+c) x =
      OpenRestriction.supportedMap f i U hU (Y.basicOpen z) N W c (n+c) y) : x = y := by
  apply SingleCechLocalizationTransport.Restricted.eq_of_map_eq
    ((f ≫ i).app U).hom W (Principal.OpenLocalization.map (f ≫ i) U hU N z) z
    ?_ ?_ c n (coefficientIso f i U hU N)
    (coefficientIso f i U hU (OpenRestriction.extension (Y.basicOpen z) N))
    (scalar f i U hU N z) (OpenRestriction.map f i U hU (Y.basicOpen z) N)
    (scalar_square f i U hU N z) (map_square f i U hU N z) x y hx hy h
  · intro r a
    obtain ⟨m, b, hb⟩ := Principal.OpenLocalization.denominators (f ≫ i) U hU N z r.unop a
    exact ⟨m, b, hb.symm⟩
  · intro r a ha
    exact Principal.OpenLocalization.kernel_power (f ≫ i) U hU N z r.unop a ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalSource.OpenFixedClass
