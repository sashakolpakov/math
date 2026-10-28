import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolutionCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Geometric Cech Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCohomology

noncomputable section

/-! Genuine geometric pullback on native frame Čech cohomology agrees in
every degree with the original bounded crystalline Ext pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of (WittVector p k))}
  {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  [IsSeparated f] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  {ι κ : Type u} (FX : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) (ρ : ι → κ)
  (α : ∀ i, (BoundedOpen.Equivalence.postcompose g hg n).obj (FX i) ⟶ FY (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "HY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) fY n
local notation "e" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Sheaves.structureTransport (p := p) (J := J) (δ := δ) g hg n

def map : BoundedFrame.CechCohomology.complex p k fY n FY ⟶
    BoundedFrame.CechCohomology.complex p k f n FX :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
    (GeometricCechCoordinates.sheafMap g hg n FX FY ρ α)

omit [CharP k p] in
theorem complexes : GeometricResolutionCech.map p k g hg n FX FY ρ α ≫
    (BoundedFrame.CechCohomology.comparison p k f n FX).hom =
      (BoundedFrame.CechCohomology.comparison p k fY n FY).hom ≫ GeometricCechCohomology.map p k g hg n FX FY ρ α := by
  let a := GeometricResolutionCech.rawMap p k g hg n FX FY ρ α
  let b := GeometricResolutionCech.coefficientMap p k g hg n FX
  let eX := (BoundedFrame.CechCohomology.comparison p k f n FX).hom
  let eY := (BoundedFrame.CechCohomology.comparison p k fY n FY).hom
  let eR := (FrameCech.Ext.Comparison.comparison.{u + 1, u, u + 2} FX R (BoundedCrystalline.Site.topology f n) ((S).obj HY)).hom
  let c := Frame.GeometricCechExt.liftedMap.{u + 1, u, u + 2} T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) HY
  let d := FrameCech.CoefficientNaturality.map.{u + 1, u, u + 2} FX R (BoundedCrystalline.Site.topology f n) (e).hom
  have ha : a ≫ eR = eY ≫ c := Frame.GeometricCechExt.complexes.{u + 1, u, u + 2}
    T FX FY ρ α R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) HY
  have hb : b ≫ eX = eR ≫ d := FrameCech.CoefficientNaturality.complexes.{u + 1, u, u + 2}
    FX R (BoundedCrystalline.Site.topology f n) (e).hom
  have hm : c ≫ d = GeometricCechCohomology.map p k g hg n FX FY ρ α :=
    (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map_comp _ _).symm
  exact (Category.assoc a b eX).trans
    ((congrArg (fun z => a ≫ z) hb).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ d) ha).trans
          ((Category.assoc _ _ _).trans (congrArg (fun z => eY ≫ z) hm)))))

variable (hX : ∀ U, CoveringObjectsSheafDetection.sieve FX U ∈ BoundedCrystalline.Site.topology f n U)
  (hY : ∀ U, CoveringObjectsSheafDetection.sieve FY U ∈ BoundedCrystalline.Site.topology fY n U)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (GeometricCechCohomology.map p k g hg n FX FY ρ α) i ≫
    (BoundedFrame.CechCohomology.homologyIso p k f n FX hX i).hom =
      (BoundedFrame.CechCohomology.homologyIso p k fY n FY hY i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let cX := BoundedFrame.CechCohomology.comparison p k f n FX
  let cY := BoundedFrame.CechCohomology.comparison p k fY n FY
  let a := GeometricResolutionCech.map p k g hg n FX FY ρ α
  let b := GeometricCechCohomology.map p k g hg n FX FY ρ α
  let d := (BoundedFrame.ResolutionCohomology.homologyIso p k f n FX hX i).hom
  have hc := InverseCoordinateHomology.homology cY cX a b (complexes p k g hg n FX FY ρ α) i
  have he := GeometricResolutionCech.homology p k g hg n FX FY ρ α hX hY i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ d) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => HomologicalComplex.homologyMap cY.inv i ≫ z) he).trans
          (Category.assoc _ _ _).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCohomology
