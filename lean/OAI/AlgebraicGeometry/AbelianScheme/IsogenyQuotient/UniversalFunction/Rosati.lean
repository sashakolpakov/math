import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.MapDetection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.DualMaps
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.Rosati
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange

/-! # Rosati -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Rosati.Construction

noncomputable section

/-! The original Rosati equation descends to the quotient over a
base with universal global functions by geometric polarization cancellation and pointed-map rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualMapBaseChange.Construction

variable {S : Scheme.{0}} {g d : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S}
  (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
  (hB : GlobalFunctions.Construction.HasUniversalGlobalFunctions B.scheme) (hDB : GlobalFunctions.Construction.HasUniversalGlobalFunctions DB.abelian.scheme)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
  (ell : A.scheme ⟶ DA.abelian.scheme)
  (m : B.scheme ⟶ DB.abelian.scheme) [IsMonHom m]
  {R : Type} [CommRing R] (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R B)
  (hσ : ∀ a : R, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)

include hB hDB hσ in
set_option backward.isDefEq.respectTransparency false in
theorem universalFunction_picardQuotient_rosati_equation (n : ℕ)
    (hp : f.hom ≫ m ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB = ell ^ n)
    (a b : R)
    (hsource : ell ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA = ρ.map b ≫ ell) :
    m ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB = σ.map b ≫ m := by
  have : IsMonHom (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (σ.map a) DB DB) :=
    DualMaps.Construction.universalFunction_nativeDualMap_isMonHom (σ.map a) DB DB hDB
  apply MapDetection.Construction.universalFunction_pointed_map_eq_of_geometric_baseChanges B.scheme DB.abelian.scheme hB
    _ _ (IsMonHom.one_hom _) (IsMonHom.one_hom _)
  intro K _ _ s
  let F := Over.pullback s
  have hσ' (c : R) : (ρ.pullback s).map c ≫ (f.pullback s).hom =
      (f.pullback s).hom ≫ (σ.pullback s).map c := by
    change F.map (ρ.map c) ≫ F.map f.hom = F.map f.hom ≫ F.map (σ.map c)
    rw [← F.map_comp, ← F.map_comp, hσ c]
  have hp' : (f.pullback s).hom ≫ F.map m ≫
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (f.pullback s).hom (DA.pullback s) (DB.pullback s) = (F.map ell) ^ n := by
    have hpow : F.map (ell ^ n) = (F.map ell) ^ n :=
      (F.homMonoidHom (X := A.scheme) (M := DA.abelian.scheme)).map_pow ell n
    have h := (congrArg F.map hp).trans hpow
    rw [F.map_comp, F.map_comp] at h
    have hd := FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange s f.hom DA DB
    change F.map (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f.hom DA DB) =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (f.pullback s).hom (DA.pullback s) (DB.pullback s) at hd
    rw [hd] at h
    exact h
  have hs' : F.map ell ≫ FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((ρ.pullback s).map a)
      (DA.pullback s) (DA.pullback s) = (ρ.pullback s).map b ≫ F.map ell := by
    have h := congrArg F.map hsource
    rw [F.map_comp, F.map_comp] at h
    have hd := FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange s (ρ.map a) DA DA
    change F.map (FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap (ρ.map a) DA DA) =
      FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap ((ρ.pullback s).map a) (DA.pullback s) (DA.pullback s) at hd
    rw [hd] at h
    exact h
  have h := Picard.Rosati.Construction.picardQuotient_rosati_equation (DA.pullback s) (DB.pullback s) (f.pullback s)
    (F.map ell) (F.map m) (ρ.pullback s) (σ.pullback s) hσ' n hp' a b hs'
  rw [Functor.map_comp, Functor.map_comp, FrobeniusKernel.DualMapBaseChange.Construction.NativePicardPullback.dualMap_baseChange]
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.Rosati.Construction
