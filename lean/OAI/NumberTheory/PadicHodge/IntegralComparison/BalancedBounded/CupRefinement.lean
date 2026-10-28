import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CupFamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.PresheafRefinement

/-! # Cup Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupRefinement

noncomputable section

/-! The native cup on original bounded crystalline Ext is invariant under
an actual refinement of covering frame families. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  {J : Ideal (WittVector p k)} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of (WittVector p k))) [IsSeparated f] (n : ℕ)
  {ι κ : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (G : κ → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (ρ : ι → κ)
  (α : ∀ i, F i ⟶ G (ρ i))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "PA" => Functor.comp (Functor.op (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n))
  (BoundedCrystalline.CechCup.structureAlgebraPresheaf f)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.forgetModule (B := WittVector p k)

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) := ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CupFamilyRefinement.Family (map complexMap complexes)

variable (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
  (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U)

omit [CharP k p] in
private theorem algebra_homology (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra f n G)).homology i) :
    HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison f n F).hom i
      (HomologicalComplex.homologyMap (Bounded.CupFamilyRefinement.Family.complexMap p k f n F G ρ α) i x) =
        HomologicalComplex.homologyMap (BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α) i
          (HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison f n G).hom i x) := by
  let c := Bounded.CupFamilyRefinement.Family.complexMap p k f n F G ρ α
  let eF := (BoundedCrystalline.CechCup.comparison f n F).hom
  let eG := (BoundedCrystalline.CechCup.comparison f n G).hom
  let a := BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α
  have hs := (HomologicalComplex.homologyMap_comp c eF i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (Bounded.CupFamilyRefinement.Family.complexes p k f n F G ρ α)).trans
      (HomologicalComplex.homologyMap_comp eG a i))
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x

private theorem lifted_natural (i : ℕ)
    (x : (BoundedFrame.CechComplex.presheafComplex f n G).homology i) :
    (CechCup.presheafHomologyIso p k f n F hF i).hom
      (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
        (BoundedFrame.CechComplex.presheafComplex f n F) i
        (HomologicalComplex.homologyMap
          (BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α) i x)) =
      (CechCup.presheafHomologyIso p k f n G hG i).hom
        (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
          (BoundedFrame.CechComplex.presheafComplex f n G) i x) := by
  let a := BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α
  have ht := congrArg (fun z => z
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n G) i x))
    (PresheafRefinement.homology p k f n F G ρ α hF hG i)
  exact (congrArg (CechCup.presheafHomologyIso p k f n F hF i).hom
    (Lifted.HomologyCoordinates.naturality.{u + 1, u + 1, u + 2} R a i x).symm).trans ht

abbrev equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra f n G)).homology i) :=
  let E := fun z => (CechCup.presheafHomologyIso p k f n F hF i).hom
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n F) i z)
  (CechCup.cohomologyEquiv_apply p k f n F hF i
    (HomologicalComplex.homologyMap (Bounded.CupFamilyRefinement.Family.complexMap p k f n F G ρ α) i x)).trans
      ((congrArg E (algebra_homology p k f n F G ρ α i x)).trans
        ((lifted_natural p k f n F G ρ α hF hG i
          (HomologicalComplex.homologyMap (BoundedCrystalline.CechCup.comparison f n G).hom i x)).trans
            (CechCup.cohomologyEquiv_apply p k f n G hG i x).symm))

include ρ α in
theorem cup_eq (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n j) :
    CechCup.cup p k f n F hF i j x y =
      CechCup.cup p k f n G hG i j x y := by
  obtain ⟨x, rfl⟩ := (CechCup.cohomologyEquiv p k f n G hG i).surjective x
  obtain ⟨y, rfl⟩ := (CechCup.cohomologyEquiv p k f n G hG j).surjective y
  let c := Bounded.CupFamilyRefinement.Family.complexMap p k f n F G ρ α
  have hn : HomologicalComplex.homologyMap c (i + j)
      (Cosimplicial.ModuleCup.cohomologyCup _ i j x y) =
        Cosimplicial.ModuleCup.cohomologyCup _ i j
          (HomologicalComplex.homologyMap c i x) (HomologicalComplex.homologyMap c j y) :=
    Cosimplicial.ModuleCup.cohomologyCup_natural (Bounded.CupFamilyRefinement.Family.map p k f n F G ρ α) i j x y
  exact (congrArg₂ (fun a b => CechCup.cup p k f n F hF i j a b)
    (equivalence_natural p k f n F G ρ α hF hG i x).symm
    (equivalence_natural p k f n F G ρ α hF hG j y).symm).trans
      ((CechCup.cup_comparison p k f n F hF i j
        (HomologicalComplex.homologyMap c i x) (HomologicalComplex.homologyMap c j y)).trans
          ((congrArg (CechCup.cohomologyEquiv p k f n F hF (i + j)) hn.symm).trans
            ((equivalence_natural p k f n F G ρ α hF hG (i + j)
              (Cosimplicial.ModuleCup.cohomologyCup _ i j x y)).trans
                (CechCup.cup_comparison p k f n G hG i j x y).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupRefinement
