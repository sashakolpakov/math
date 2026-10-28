import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.Homotopy

/-! # Pulled Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledHomology

noncomputable section

/-! Geometric frame comparison yields the original coefficient-linear restriction identity on homology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  (FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n FX)]
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg n I
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B))
  (BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n) 0

def globalComparison :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamSections.frameComplex fY n FY) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (IX).cocomplex :=
  ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (DeRhamSections.frameComplex fY n FY) (IX).cocomplex
    (PulledMap.map g hg n (FY := FY) ≫
      GeometricHomotopy.globalMap g hg n FY I)

def localComparison :
    ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).obj
      (DeRhamSections.frameComplex fY n FY) ⟶
    ((S).mapHomologicalComplex (.up ℕ)).obj (IX).cocomplex :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapHomologicalComplex (.up ℕ)).map
    (SectionChange.frameMap α) ≫ DeRhamSections.sectionsMap f n FX ≫
      ((S).mapHomologicalComplex (.up ℕ)).map (Injective.Comparison.map f n FX IX)

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)] in
theorem local_component (i : ℕ) :
    (ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
      (DeRhamSections.frameComplex fY n FY) (IX).cocomplex
      (PulledMap.map g hg n (FY := FY) ≫
        GeometricHomotopy.localMap g hg n FY I FX α)).f i =
          (localComparison g hg n FY I FX α).f i := by
  let T := S
  have h := ConstantSection.ComplexComposition.component.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n) (DeRhamSections.frameComplex fY n FY)
    (PulledMap.map g hg n (FY := FY))
    (GeometricHomotopy.localMap g hg n FY I FX α) i
  exact h.trans
    ((congrArg (fun a =>
      (ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
        (DeRhamSections.frameComplex fY n FY) _
        (PulledMap.map g hg n (FY := FY))).f i ≫ a)
      (T.map_comp ((GeometricMap.map g hg n α).f i)
        ((Injective.Comparison.map f n FX IX).f i))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun a => a ≫ T.map ((Injective.Comparison.map f n FX IX).f i))
          (PulledMap.sections_component g hg n α i)).trans (Category.assoc _ _ _))))

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)] in
theorem local_eq : ConstantSection.ComplexMap.map.{u + 1, u, u + 1, u + 2}
    (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (DeRhamSections.frameComplex fY n FY) (IX).cocomplex
    (PulledMap.map g hg n (FY := FY) ≫
      GeometricHomotopy.localMap g hg n FY I FX α) = localComparison g hg n FY I FX α := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact local_component g hg n FY I FX α i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (globalComparison g hg n FY I) i =
    HomologicalComplex.homologyMap (localComparison g hg n FY I FX α) i :=
  (ConstantSection.Homotopy.homology.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (DeRhamSections.frameComplex fY n FY) (PulledMap.map g hg n (FY := FY))
    (GeometricHomotopy.globalMap g hg n FY I)
    (GeometricHomotopy.localMap g hg n FY I FX α)
    (GeometricHomotopy.homotopy g hg n FY I FX α) i).trans
      (congrArg (fun a => HomologicalComplex.homologyMap a i) (local_eq g hg n FY I FX α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledHomology
