import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCechCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CupFamilyRefinement

/-! # Geometric Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCupNaturality

noncomputable section

/-! Native frame cup products are natural for actual scheme morphisms on
the original bounded crystalline Ext groups. No lift of the scheme map
to a chosen global smooth model is assumed. -/

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
local notation "TX" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n))
  (BoundedCrystalline.CechCup.structureAlgebraPresheaf f)
local notation "TY" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n))
  (BoundedCrystalline.CechCup.structureAlgebraPresheaf fY)
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.forgetModule (B := WittVector p k)

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

omit [CharP k p] in
theorem algebraComplexes : BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α ≫
    (BoundedCrystalline.CechCup.comparison f n FX).hom =
      (BoundedCrystalline.CechCup.comparison fY n FY).hom ≫
        GeometricCechCoordinates.presheafMap g hg n FX FY ρ α := by
  apply HomologicalComplex.Hom.ext
  funext a
  exact (congrArg (fun z => (BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α).f a ≫ z)
    (CupFamilyRefinement.Family.comparison_f p k f n FX a)).trans
      ((Frame.CosimplicialRefinement.piComparison_reindex
        (fun t : Fin (a + 1) → ι => ρ ∘ t) U
        (P := fun t => (TY).obj (op (Presentation.TupleProducts.family.{u + 1, u} FY a t)))
        (Q := fun t => (TX).obj (op (Presentation.TupleProducts.family.{u + 1, u} FX a t)))
        (BoundedCrystalline.CupRefinement.coefficient g hg n FX FY ρ α a)).trans
          (congrArg (fun z => z ≫ (GeometricCechCoordinates.presheafMap g hg n FX FY ρ α).f a)
            (CupFamilyRefinement.Family.comparison_f p k fY n FY a)).symm)

def liftedPresheafMap : BoundedFrame.CechPresheafCohomology.complex p k fY n FY ⟶
    BoundedFrame.CechPresheafCohomology.complex p k f n FX :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
    (GeometricCechCoordinates.presheafMap g hg n FX FY ρ α)

omit [CharP k p] in
theorem presheafComplexes : liftedPresheafMap p k g hg n FX FY ρ α ≫
    (BoundedFrame.CechPresheafCohomology.sheafIso p k f n FX).hom =
      (BoundedFrame.CechPresheafCohomology.sheafIso p k fY n FY).hom ≫
        GeometricCechCohomology.map p k g hg n FX FY ρ α := by
  let L := (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)
  exact (L.map_comp _ _).symm.trans
    ((congrArg L.map (GeometricCechCoordinates.complexes g hg n FX FY ρ α)).trans (L.map_comp _ _))

variable (hX : ∀ V, CoveringObjectsSheafDetection.sieve FX V ∈ BoundedCrystalline.Site.topology f n V)
  (hY : ∀ V, CoveringObjectsSheafDetection.sieve FY V ∈ BoundedCrystalline.Site.topology fY n V)

theorem presheafHomology (i : ℕ) : HomologicalComplex.homologyMap
    (liftedPresheafMap p k g hg n FX FY ρ α) i ≫
      (BoundedFrame.CechPresheafCohomology.homologyIso p k f n FX hX i).hom =
        (BoundedFrame.CechPresheafCohomology.homologyIso p k fY n FY hY i).hom ≫
          ModuleCat.ofHom (BoundedCrystalline.CrystallinePullback.pullback g hg n i) := by
  let a := liftedPresheafMap p k g hg n FX FY ρ α
  let b := (BoundedFrame.CechPresheafCohomology.sheafIso p k f n FX).hom
  let c := (BoundedFrame.CechPresheafCohomology.sheafIso p k fY n FY).hom
  let d := GeometricCechCohomology.map p k g hg n FX FY ρ α
  let h := (BoundedFrame.CechCohomology.homologyIso p k f n FX hX i).hom
  have hs := (HomologicalComplex.homologyMap_comp a b i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (presheafComplexes p k g hg n FX FY ρ α)).trans
      (HomologicalComplex.homologyMap_comp c d i))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ h) hs).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => HomologicalComplex.homologyMap c i ≫ z)
          (GeometricCechCohomology.homology p k g hg n FX FY ρ α hX hY i)).trans
            (Category.assoc _ _ _).symm)))

theorem equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra fY n FY)).homology i) :
    BoundedCrystalline.CechCup.cohomologyEquiv p k f n FX hX i
      (HomologicalComplex.homologyMap (BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α) i x) =
        BoundedCrystalline.CrystallinePullback.pullback g hg n i
          (BoundedCrystalline.CechCup.cohomologyEquiv p k fY n FY hY i x) := by
  let c := BoundedCrystalline.CupRefinement.complexMap g hg n FX FY ρ α
  let eX := (BoundedCrystalline.CechCup.comparison f n FX).hom
  let eY := (BoundedCrystalline.CechCup.comparison fY n FY).hom
  let a := GeometricCechCoordinates.presheafMap g hg n FX FY ρ α
  have hs := (HomologicalComplex.homologyMap_comp c eX i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (algebraComplexes p k g hg n FX FY ρ α)).trans
      (HomologicalComplex.homologyMap_comp eY a i))
  let E := (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
    (BoundedFrame.CechComplex.presheafComplex f n FX) i).trans
      (BoundedFrame.CechPresheafCohomology.homologyIso p k f n FX hX i).toLinearEquiv
  have ht := congrArg (fun z => z
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex fY n FY) i (HomologicalComplex.homologyMap eY i x)))
    (presheafHomology p k g hg n FX FY ρ α hX hY i)
  exact (congrArg E (congrArg (fun z => z x) hs)).trans
    ((congrArg (BoundedFrame.CechPresheafCohomology.homologyIso p k f n FX hX i).hom
      (Lifted.HomologyCoordinates.naturality.{u + 1, u + 1, u + 2} R a i
        (HomologicalComplex.homologyMap eY i x)).symm).trans ht)

include ρ α in
theorem cup_natural (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n j) :
    BoundedCrystalline.CrystallinePullback.pullback g hg n (i + j)
      (BoundedCrystalline.CechCup.cup p k fY n FY hY i j x y) =
        BoundedCrystalline.CechCup.cup p k f n FX hX i j
          (BoundedCrystalline.CrystallinePullback.pullback g hg n i x)
          (BoundedCrystalline.CrystallinePullback.pullback g hg n j y) := by
  obtain ⟨x, rfl⟩ := (BoundedCrystalline.CechCup.cohomologyEquiv p k fY n FY hY i).surjective x
  obtain ⟨y, rfl⟩ := (BoundedCrystalline.CechCup.cohomologyEquiv p k fY n FY hY j).surjective y
  rw [BoundedCrystalline.CechCup.cup_comparison,
    ← equivalence_natural p k g hg n FX FY ρ α hX hY]
  have hn := BoundedCrystalline.CupRefinement.cohomologyCup_natural g hg n FX FY ρ α i j x y
  exact (congrArg (BoundedCrystalline.CechCup.cohomologyEquiv p k f n FX hX (i + j)) hn).trans
    ((BoundedCrystalline.CechCup.cup_comparison p k f n FX hX i j _ _).symm.trans
      (congrArg₂ (fun a b => BoundedCrystalline.CechCup.cup p k f n FX hX i j a b)
        (equivalence_natural p k g hg n FX FY ρ α hX hY i x)
        (equivalence_natural p k g hg n FX FY ρ α hX hY j y)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCupNaturality
