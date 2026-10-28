import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionSheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import Mathlib.Topology.Sheaves.Flasque

/-! # Flasque Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

noncomputable section

/-!
# IntegralComparison: the original bounded crystalline resolution gives a complex of flasque Zariski sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

instance ulift_sheafCompose : (Opens.grothendieckTopology Y).HasSheafCompose
    (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) := by
  let : Limits.PreservesLimitsOfSize.{u, u}
      (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) :=
    Limits.preservesLimitsOfSize_of_univLE.{u + 1, u + 1} _
  infer_instance

def functor : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n ⥤
    Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  SectionSheaf.functor fY n ⋙
    sheafCompose (Opens.grothendieckTopology Y) (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))

instance functor_additive : (functor (p := p) (J := J) (δ := δ) fY n).Additive where
  map_add := by intros; rfl

def underlyingIso : functor (p := p) (J := J) (δ := δ) fY n ⋙
    sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ≅
      SectionComplex.functor fY n := Iso.refl _

theorem flasque (F : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n)
    [Injective F] : TopCat.Presheaf.IsFlasque (X := Y.carrier) (((functor fY n).obj F).obj) where
  epi α := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨y, hy⟩ := SectionPresheaf.restriction_surjective fY n F α x.down
    exact ⟨ULift.up y, congrArg ULift.up hy⟩

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def complex : CochainComplex
    (Sheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))) ℕ :=
  ((functor fY n).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

def underlyingComplexIso :
    ((sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B)))).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (complex fY n I) ≅ SectionComplex.complex fY n I := Iso.refl _

theorem term_flasque (i : ℕ) :
    TopCat.Presheaf.IsFlasque (X := Y.carrier) (((complex fY n I).X i).obj) := by
  let : Injective (I.cocomplex.X i) := I.injective i
  exact flasque fY n (I.cocomplex.X i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex
