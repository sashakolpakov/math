import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Coordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainUnit

/-! # Constant Cochain Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates

noncomputable section

/-! The canonical section of a sheafified constant-presheaf cochain
map evaluates to the literal sheafification-unit image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v z
variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{u} R)]
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

local notation "S" => presheafToSheaf J (ModuleCat R)

def sheafComplex := ((S).mapHomologicalComplex (.up ℕ)).obj P

def sheafMap : ((constantSheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj M ⟶
    sheafComplex R J P := ((S).mapHomologicalComplex (.up ℕ)).map a

def sectionMap := ConstantSection.ComplexMap.map R J M
  (sheafComplex R J P) (sheafMap R J M P a)

theorem coordinates (q : ℕ) (x : M.X q) (V : Cᵒᵖ) :
    (Ext.ZeroPresheafSections.equivalence.{u,v,u,z} R J ((sheafComplex R J P).X q)
      ((sectionMap R J M P a).f q (ULift.up x))).down.app V (1 : R) =
        ((sheafificationAdjunction J (ModuleCat.{u} R)).unit.app (P.X q)).app V
          ((a.f q).app V x) := by
  have h := ConstantSection.Coordinates.section_apply.{u,v,u,z} R J (M.X q)
    ((sheafComplex R J P).X q) ((sheafMap R J M P a).f q) x V (1 : R)
  have hn := (sheafificationAdjunction J (ModuleCat.{u} R)).unit.naturality (a.f q)
  change _ = _ at h
  exact h.trans (by
    change (((sheafificationAdjunction J (ModuleCat.{u} R)).unit.app
      (((Functor.const Cᵒᵖ).obj (M.X q)))).app V ≫
        ((S).map (a.f q)).hom.app V) ((1 : R) • x) = _
    rw [one_smul]
    exact (ConcreteCategory.congr_hom (congrArg (fun b => b.app V) hn) x).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates
