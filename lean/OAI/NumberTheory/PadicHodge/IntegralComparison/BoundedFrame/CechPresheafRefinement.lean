import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafCohomology

/-! # Cech Presheaf Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafRefinement

noncomputable section

/-! Refinement invariance for the actual ambient-ring presheaf Čech
comparison with original bounded crystalline Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "P" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion f n)) (OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.largePresheaf f)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f n

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

def map : CechComplex.presheafComplex f n G ⟶
    CechComplex.presheafComplex f n F :=
  (AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat R)).map
    (Cech.FamilyRefinement.Family.map.{u + 1, u} F G ρ α P)

def liftedMap : CechPresheafCohomology.complex p k f n G ⟶
    CechPresheafCohomology.complex p k f n F :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map (CechPresheafRefinement.map p k f n F G ρ α)

omit [CharP k p] in
theorem coefficientComplexes : CechPresheafRefinement.map p k f n F G ρ α ≫ (CechComplex.presheafIso f n F).hom =
    (CechComplex.presheafIso f n G).hom ≫
      FrameCech.RefinementExt.cochainMap.{u + 1, u} F G ρ α R (BoundedCrystalline.Site.topology f n) H := by
  let e := Functor.isoWhiskerLeft (BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op
    (Crystalline.StructureDescent.structurePresheafIso (p := p) (J := J) (δ := δ) f)
  let T := AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{u + 1} R)
  have h := Cech.FamilyRefinement.Family.naturality.{u + 1, u} F G ρ α P (H).obj e.hom
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h.symm).trans (T.map_comp _ _))

omit [CharP k p] in
theorem complexes : liftedMap p k f n F G ρ α ≫
    (CechPresheafCohomology.sheafIso p k f n F).hom =
      (CechPresheafCohomology.sheafIso p k f n G).hom ≫
        CechRefinement.map p k f n F G ρ α := by
  let T := (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map (coefficientComplexes p k f n F G ρ α)).trans (T.map_comp _ _))

theorem homology
    (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
    (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U) (i : ℕ) :
    HomologicalComplex.homologyMap (liftedMap p k f n F G ρ α) i ≫
      (CechPresheafCohomology.homologyIso p k f n F hF i).hom =
        (CechPresheafCohomology.homologyIso p k f n G hG i).hom := by
  let a := liftedMap p k f n F G ρ α
  let b := (CechPresheafCohomology.sheafIso p k f n F).hom
  let c := (CechPresheafCohomology.sheafIso p k f n G).hom
  let d := CechRefinement.map p k f n F G ρ α
  let h := (CechCohomology.homologyIso p k f n F hF i).hom
  have hs := (HomologicalComplex.homologyMap_comp a b i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (complexes p k f n F G ρ α)).trans
      (HomologicalComplex.homologyMap_comp c d i))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ h) hs).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun z => HomologicalComplex.homologyMap c i ≫ z)
          (CechRefinement.homology p k f n F G ρ α hF hG i))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafRefinement
