import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCupNaturality

/-! # Geometric Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricCup

noncomputable section

/-! The balanced native cup on original bounded crystalline Ext is natural
for genuine geometric maps and covering-frame refinements. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCupNaturality

variable (hX : ∀ V, CoveringObjectsSheafDetection.sieve FX V ∈ BoundedCrystalline.Site.topology f n V)
  (hY : ∀ V, CoveringObjectsSheafDetection.sieve FY V ∈ BoundedCrystalline.Site.topology fY n V)

theorem sheafHomology (i : ℕ) : HomologicalComplex.homologyMap (Bounded.GeometricCechCohomology.map p k g hg n FX FY ρ α) i ≫
    (CechCup.sheafHomologyIso p k f n FX hX i).hom =
      (CechCup.sheafHomologyIso p k fY n FY hY i).hom ≫
        ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let cX := BoundedFrame.CechCohomology.comparison p k f n FX
  let cY := BoundedFrame.CechCohomology.comparison p k fY n FY
  let a := Bounded.GeometricResolutionCech.map p k g hg n FX FY ρ α
  let b := Bounded.GeometricCechCohomology.map p k g hg n FX FY ρ α
  let d := (CechCup.resolutionHomologyIso p k f n FX hX i).hom
  have hc := InverseCoordinateHomology.homology cY cX a b (Bounded.GeometricCechCohomology.complexes p k g hg n FX FY ρ α) i
  have he := GeometricResolution.homology p k g hg n FX FY ρ α hX hY i
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ d) hc).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => HomologicalComplex.homologyMap cY.inv i ≫ z) he).trans
          (Category.assoc _ _ _).symm)))

theorem presheafHomology (i : ℕ) : HomologicalComplex.homologyMap
    (Bounded.GeometricCupNaturality.liftedPresheafMap p k g hg n FX FY ρ α) i ≫
      (CechCup.presheafHomologyIso p k f n FX hX i).hom =
        (CechCup.presheafHomologyIso p k fY n FY hY i).hom ≫
          ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let a := Bounded.GeometricCupNaturality.liftedPresheafMap p k g hg n FX FY ρ α
  let b := (BoundedFrame.CechPresheafCohomology.sheafIso p k f n FX).hom
  let c := (BoundedFrame.CechPresheafCohomology.sheafIso p k fY n FY).hom
  let d := Bounded.GeometricCechCohomology.map p k g hg n FX FY ρ α
  let h := (CechCup.sheafHomologyIso p k f n FX hX i).hom
  have hs := (HomologicalComplex.homologyMap_comp a b i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (Bounded.GeometricCupNaturality.presheafComplexes p k g hg n FX FY ρ α)).trans
      (HomologicalComplex.homologyMap_comp c d i))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ h) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => HomologicalComplex.homologyMap c i ≫ z)
          (sheafHomology p k g hg n FX FY ρ α hX hY i)).trans
            (Category.assoc _ _ _).symm)))

private theorem lifted_presheaf_natural (i : ℕ)
    (z : (BoundedFrame.CechComplex.presheafComplex fY n FY).homology i) :
    (CechCup.presheafHomologyIso p k f n FX hX i).hom
      (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
        (BoundedFrame.CechComplex.presheafComplex f n FX) i
        (HomologicalComplex.homologyMap
          (Bounded.GeometricCechCoordinates.presheafMap g hg n FX FY ρ α) i z)) =
      BoundedCrystalline.CrystallinePullback.pullback g hg n i
        ((CechCup.presheafHomologyIso p k fY n FY hY i).hom
          (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
            (BoundedFrame.CechComplex.presheafComplex fY n FY) i z)) := by
  let a := Bounded.GeometricCechCoordinates.presheafMap g hg n FX FY ρ α
  have ht := congrArg (fun b => b
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex fY n FY) i z))
    (presheafHomology p k g hg n FX FY ρ α hX hY i)
  exact (congrArg (CechCup.presheafHomologyIso p k f n FX hX i).hom
    (Lifted.HomologyCoordinates.naturality.{u + 1, u + 1, u + 2} R a i z).symm).trans ht

omit [CharP k p] in
private theorem algebra_homology (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra fY n FY)).homology i) :
    HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison f n FX).hom i
      (HomologicalComplex.homologyMap
        (BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α) i x) =
      HomologicalComplex.homologyMap (Bounded.GeometricCechCoordinates.presheafMap g hg n FX FY ρ α) i
        (HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison fY n FY).hom i x) := by
  let c := BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α
  let eX := (BoundedCrystalline.CechCup.comparison f n FX).hom
  let eY := (BoundedCrystalline.CechCup.comparison fY n FY).hom
  let a := Bounded.GeometricCechCoordinates.presheafMap g hg n FX FY ρ α
  have hs := (HomologicalComplex.homologyMap_comp c eX i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (Bounded.GeometricCupNaturality.algebraComplexes p k g hg n FX FY ρ α)).trans
      (HomologicalComplex.homologyMap_comp eY a i))
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x

def EquivalenceNaturality (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra fY n FY)).homology i) : Prop :=
    CechCup.cohomologyEquiv p k f n FX hX i
      (HomologicalComplex.homologyMap (BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α) i x) =
        BoundedCrystalline.CrystallinePullback.pullback g hg n i
          (CechCup.cohomologyEquiv p k fY n FY hY i x)

abbrev equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra fY n FY)).homology i) :=
  let c := BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α
  let eY := (BoundedCrystalline.CechCup.comparison fY n FY).hom
  let E := fun z => (CechCup.presheafHomologyIso p k f n FX hX i).hom
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n FX) i z)
  (CechCup.cohomologyEquiv_apply p k f n FX hX i
    (HomologicalComplex.homologyMap c i x)).trans
      ((congrArg E (algebra_homology p k g hg n FX FY ρ α i x)).trans
        ((lifted_presheaf_natural p k g hg n FX FY ρ α hX hY i
          (HomologicalComplex.homologyMap eY i x)).trans
            (congrArg (BoundedCrystalline.CrystallinePullback.pullback g hg n i)
              (CechCup.cohomologyEquiv_apply p k fY n FY hY i x).symm)))

include ρ α in
theorem cup_natural (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n j) :
    BoundedCrystalline.CrystallinePullback.pullback g hg n (i + j)
      (CechCup.cup p k fY n FY hY i j x y) =
        CechCup.cup p k f n FX hX i j
          (BoundedCrystalline.CrystallinePullback.pullback g hg n i x)
          (BoundedCrystalline.CrystallinePullback.pullback g hg n j y) := by
  obtain ⟨x, rfl⟩ := (CechCup.cohomologyEquiv p k fY n FY hY i).surjective x
  obtain ⟨y, rfl⟩ := (CechCup.cohomologyEquiv p k fY n FY hY j).surjective y
  rw [CechCup.cup_comparison,
    ← equivalence_natural p k g hg n FX FY ρ α hX hY]
  have hn := BoundedCrystalline.CupRefinement.cohomologyCup_natural g hg n FX FY ρ α i j x y
  exact (congrArg (CechCup.cohomologyEquiv p k f n FX hX (i + j)) hn).trans
    ((CechCup.cup_comparison p k f n FX hX i j _ _).symm.trans
      (congrArg₂ (fun a b => CechCup.cup p k f n FX hX i j a b)
        (equivalence_natural p k g hg n FX FY ρ α hX hY i x)
        (equivalence_natural p k g hg n FX FY ρ α hX hY j y)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.GeometricCup
