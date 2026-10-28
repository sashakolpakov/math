import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.IsoTransportNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Resolution Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionExt

noncomputable section

/-! The geometric map between the original bounded crystalline resolutions computes the original Ext pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

private theorem iso_square {D : Type*} [Category* D]
    {S T A B : D} (s : S ≅ T) (a : S ⟶ A) (b : A ⟶ B) (d : T ⟶ B)
    (h : (s.inv ≫ a) ≫ b = d) : a ≫ b = s.hom ≫ d := by
  rw [← h, ← Category.assoc, ← Category.assoc, s.hom_inv_id, Category.id_comp]

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (IY : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  (IX : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "AX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n
local notation "AY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) fY n
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n
local notation "t" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallinePullback.constantTransport (p := p) (J := J) (δ := δ) g hg n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionMap.map g hg n IY IX

theorem augmentation_square : (F).map (IY.ι.f 0) ≫ (e).f 0 = (s).hom ≫ IX.ι.f 0 :=
  iso_square s _ _ _
    ((congrArg (fun a => a ≫ (e).f 0)
      (ResolutionMap.augmentation_zero g hg n IY).symm).trans
        (congrArg (fun a => a.f 0) (ResolutionMap.map_augmentation g hg n IY IX)))

def sectionMap : InjectiveSectionCohomology.complex R AY IY ⟶
    InjectiveSectionCohomology.complex R AX IX :=
  AlgebraicGeometry.Crystalline.Cohomology.Acyclic.TransportNaturality.AcyclicTransportNaturality.sectionMap R F AY (t).inv e

theorem naturality (i : ℕ) (x : (InjectiveSectionCohomology.complex R AY IY).homology i) :
    (InjectiveSectionCohomology.homologyIso R AX IX i).hom
      (HomologicalComplex.homologyMap (sectionMap g hg n IY IX) i x) =
    BoundedCrystalline.CrystallinePullback.pullback g hg n i
      ((InjectiveSectionCohomology.homologyIso R AY IY i).hom x) := by
  exact Acyclic.IsoTransportNaturality.naturality R F AY t e IY.ι IX.ι s
    (augmentation_square g hg n IY IX)
    (fun j q => Abelian.Ext.subsingleton_of_injective AY (IY.cocomplex.X j) q)
    (fun j q => Abelian.Ext.subsingleton_of_injective ((F).obj AY) (IX.cocomplex.X j) q)
    (fun j q => Abelian.Ext.subsingleton_of_injective AX (IX.cocomplex.X j) q) i x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionExt
