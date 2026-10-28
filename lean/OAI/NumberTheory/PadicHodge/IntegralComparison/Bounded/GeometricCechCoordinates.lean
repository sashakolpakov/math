import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.GeometricCechExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CupRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.FunctorCoordinates

/-! # Geometric Cech Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCoordinates

noncomputable section

/-! The native geometric ring Čech map has exactly the original sheaf
coordinates, including the canonical crystalline coefficient transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {ι κ : Type u} (FX : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) (ρ : ι → κ)
  (α : ∀ i, (BoundedOpen.Equivalence.postcompose g hg n).obj (FX i) ⟶ FY (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "PX" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n))
  (BigCrystallineCohomology.largePresheaf f)
local notation "PY" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n))
  (BigCrystallineCohomology.largePresheaf fY)
local notation "HY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n
local notation "HX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.forgetModule (B := B)

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

def coefficient (a : ℕ) (t : Fin (a + 1) → ι) :
    (PY).obj (op (Presentation.TupleProducts.family.{u + 1, u} FY a (ρ ∘ t))) ⟶
      (PX).obj (op (Presentation.TupleProducts.family.{u + 1, u} FX a t)) :=
  (PY).map (Frame.TupleRefinement.map.{u + 1, u} T FX FY ρ α a t).op

theorem coefficient_naturality (a b : ℕ) (θ : Fin (b + 1) → Fin (a + 1)) (t : Fin (a + 1) → ι) :
    coefficient g hg n FX FY ρ α b (t ∘ θ) ≫
        (PX).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FX θ t).op =
      (PY).map (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FY θ (ρ ∘ t)).op ≫
        coefficient g hg n FX FY ρ α a t :=
  ((U).map_comp
    (BoundedCrystalline.CupRefinement.coefficient g hg n FX FY ρ α b (t ∘ θ))
    (((BoundedCrystalline.Site.inclusion f n).op ⋙ BoundedCrystalline.CechCup.structureAlgebraPresheaf f).map
      (Presentation.ResolutionFaceMaps.productMap.{u + 1, u} FX θ t).op)).symm.trans
    ((congrArg (U).map (BoundedCrystalline.CupRefinement.coefficient_naturality
      g hg n FX FY ρ α a b θ t)).trans ((U).map_comp _ _))

def presheafMap : BoundedFrame.CechComplex.presheafComplex fY n FY ⟶
    BoundedFrame.CechComplex.presheafComplex f n FX :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map
    (Frame.CosimplicialRefinement.map.{u + 1, u} FY FX ρ PY PX
      (coefficient g hg n FX FY ρ α) (coefficient_naturality g hg n FX FY ρ α))

def coefficientMap : FrameCech.Differential.complex.{u + 1, u} FX R ((S).obj HY).obj ⟶
    BoundedFrame.CechComplex.complex f n FX :=
  (NonemptyCechNerve.complexFunctor FX).map (e).hom.hom

def sheafMap : BoundedFrame.CechComplex.complex fY n FY ⟶
    BoundedFrame.CechComplex.complex f n FX :=
  Frame.GeometricCechExt.cochainMap.{u + 1, u} T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) HY ≫
    coefficientMap g hg n FX

theorem coefficient_square (a : ℕ) (t : Fin (a + 1) → ι) :
    coefficient g hg n FX FY ρ α a t ≫
      (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) f n).hom.app
        (op (Presentation.TupleProducts.family.{u + 1, u} FX a t)) =
    (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) fY n).hom.app
      (op (Presentation.TupleProducts.family.{u + 1, u} FY a (ρ ∘ t))) ≫
        (HY).obj.map (Frame.TupleRefinement.map.{u + 1, u} T FX FY ρ α a t).op ≫
          (e).hom.hom.app (op (Presentation.TupleProducts.family.{u + 1, u} FX a t)) := by
  let V := op (Presentation.TupleProducts.family.{u + 1, u} FX a t)
  let W := op (Presentation.TupleProducts.family.{u + 1, u} FY a (ρ ∘ t))
  let b := (Frame.TupleRefinement.map.{u + 1, u} T FX FY ρ α a t).op
  let eX := (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) f n).hom
  let eY := (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) fY n).hom
  have ht : eY.app ((T).op.obj V) ≫ (e).hom.hom.app V = eX.app V :=
    (congrArg (fun z => z.app V) (StructureCoordinates.coordinates n g hg)).trans (Category.id_comp _)
  have hn : (PY).map b ≫ eY.app ((T).op.obj V) = eY.app W ≫ (HY).obj.map b := eY.naturality b
  exact (congrArg (fun z => coefficient g hg n FX FY ρ α a t ≫ z) ht.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (e).hom.hom.app V) hn).trans (Category.assoc _ _ _)))

theorem complexes : presheafMap g hg n FX FY ρ α ≫
    (BoundedFrame.CechComplex.presheafIso f n FX).hom =
      (BoundedFrame.CechComplex.presheafIso fY n FY).hom ≫ sheafMap g hg n FX FY ρ α := by
  apply HomologicalComplex.Hom.ext
  funext a
  apply Pi.hom_ext
  intro t
  let VX := op (Presentation.TupleProducts.family.{u + 1, u} FX a t)
  let VY := op (Presentation.TupleProducts.family.{u + 1, u} FY a (ρ ∘ t))
  let πPX := FrameCech.Differential.coordinate.{u + 1, u} FX R PX a t
  let πPY := FrameCech.Differential.coordinate.{u + 1, u} FY R PY a (ρ ∘ t)
  let πHX := FrameCech.Differential.coordinate.{u + 1, u} FX R (HX).obj a t
  let πHY := FrameCech.Differential.coordinate.{u + 1, u} FY R (HY).obj a (ρ ∘ t)
  let πH := FrameCech.Differential.coordinate.{u + 1, u} FX R ((S).obj HY).obj a t
  let c := coefficient g hg n FX FY ρ α a t
  let b := (HY).obj.map (Frame.TupleRefinement.map.{u + 1, u} T FX FY ρ α a t).op
  let eX := (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) f n).hom.app VX
  let eY := (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) fY n).hom.app VY
  let s := (e).hom.hom.app VX
  let q := (presheafMap g hg n FX FY ρ α).f a
  let h := (sheafMap g hg n FX FY ρ α).f a
  let u := (BoundedFrame.CechComplex.presheafIso f n FX).hom.f a
  let v := (BoundedFrame.CechComplex.presheafIso fY n FY).hom.f a
  let m := (Frame.GeometricCechExt.cochainMap.{u + 1, u}
    T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) HY).f a
  let d := (coefficientMap g hg n FX).f a
  have hu : u ≫ πHX = πPX ≫ eX :=
    FrameCech.FunctorCoordinates.coordinate.{u + 1, u} FX R
      (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) f n).hom a t
  have hv : v ≫ πHY = πPY ≫ eY :=
    FrameCech.FunctorCoordinates.coordinate.{u + 1, u} FY R
      (StructureCoordinates.presheafIso (p := p) (J := J) (δ := δ) fY n).hom a (ρ ∘ t)
  have hq : q ≫ πPX = πPY ≫ c := Pi.lift_comp_π _ t
  have hm : m ≫ πH = πHY ≫ b :=
    Frame.GeometricCechExt.cochainMap_coordinate.{u + 1, u}
      T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) HY a t
  have hd : d ≫ πHX = πH ≫ s := FrameCech.FunctorCoordinates.coordinate FX R (e).hom.hom a t
  have hh : h ≫ πHX = πHY ≫ (b ≫ s) :=
    (Category.assoc m d πHX).trans
      ((congrArg (fun z => m ≫ z) hd).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ s) hm).trans (Category.assoc _ _ _))))
  have hl : (q ≫ u) ≫ πHX = πPY ≫ (c ≫ eX) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => q ≫ z) hu).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ eX) hq).trans (Category.assoc _ _ _))))
  have hr : (v ≫ h) ≫ πHX = πPY ≫ (eY ≫ b ≫ s) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z => v ≫ z) hh).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ (b ≫ s)) hv).trans (Category.assoc _ _ _))))
  exact hl.trans ((congrArg (fun z => πPY ≫ z) (coefficient_square g hg n FX FY ρ α a t)).trans hr.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCoordinates
