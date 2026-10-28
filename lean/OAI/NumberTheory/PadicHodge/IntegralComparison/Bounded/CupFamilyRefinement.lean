import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechPresheafRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup

/-! # Cup Family Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CupFamilyRefinement.Family

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

def map : BoundedCrystalline.CechCup.cochainAlgebra f n G ⟶
    BoundedCrystalline.CechCup.cochainAlgebra f n F :=
  Cech.FamilyRefinement.Family.map.{u + 1, u} F G ρ α PA

def complexMap := Cosimplicial.ModuleCup.complexMap (Family.map p k f n F G ρ α)

omit [CharP k p] in
theorem comparison_f (a : ℕ) : (BoundedCrystalline.CechCup.comparison f n F).hom.f a =
    piComparison T (fun t : Fin (a + 1) → ι =>
      (PA).obj (op (Presentation.TupleProducts.family.{u + 1, u} F a t))) := by
  let Q := fun t : Fin (a + 1) → ι =>
    (PA).obj (op (Presentation.TupleProducts.family.{u + 1, u} F a t))
  let C := NonemptyCechNerve.complexFunctor (A := ModuleCat.{u + 1} R) F
  let H := (BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙
    BigCrystallineCohomology.largePresheaf f
  change piComparison T Q ≫ (C.map (𝟙 H)).f a = piComparison T Q
  exact (congrArg (fun z => piComparison T Q ≫ z.f a) (C.map_id H)).trans (Category.comp_id _)

omit [CharP k p] in
theorem complexes : complexMap p k f n F G ρ α ≫
    (BoundedCrystalline.CechCup.comparison f n F).hom =
      (BoundedCrystalline.CechCup.comparison f n G).hom ≫
        BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α := by
  apply HomologicalComplex.Hom.ext
  funext a
  exact (congrArg (fun z => (complexMap p k f n F G ρ α).f a ≫ z)
    (comparison_f p k f n F a)).trans
      ((Frame.CosimplicialRefinement.piComparison_reindex
        (fun t : Fin (a + 1) → ι => ρ ∘ t) T
        (P := fun t => (PA).obj (op (Presentation.TupleProducts.family.{u + 1, u} G a t)))
        (Q := fun t => (PA).obj (op (Presentation.TupleProducts.family.{u + 1, u} F a t)))
        (Cech.FamilyRefinement.Family.coefficient.{u + 1, u} F G ρ α PA a)).trans
          (congrArg (fun z => z ≫ (BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α).f a)
            (comparison_f p k f n G a)).symm)

variable (hF : ∀ U, CoveringObjectsSheafDetection.sieve F U ∈ BoundedCrystalline.Site.topology f n U)
  (hG : ∀ U, CoveringObjectsSheafDetection.sieve G U ∈ BoundedCrystalline.Site.topology f n U)

theorem equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex
      (BoundedCrystalline.CechCup.cochainAlgebra f n G)).homology i) :
    BoundedCrystalline.CechCup.cohomologyEquiv p k f n F hF i
      (HomologicalComplex.homologyMap (complexMap p k f n F G ρ α) i x) =
        BoundedCrystalline.CechCup.cohomologyEquiv p k f n G hG i x := by
  let c := complexMap p k f n F G ρ α
  let eF := (BoundedCrystalline.CechCup.comparison f n F).hom
  let eG := (BoundedCrystalline.CechCup.comparison f n G).hom
  let a := BoundedFrame.CechPresheafRefinement.map p k f n F G ρ α
  have hs := (HomologicalComplex.homologyMap_comp c eF i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (complexes p k f n F G ρ α)).trans
      (HomologicalComplex.homologyMap_comp eG a i))
  let EF := (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
    (BoundedFrame.CechComplex.presheafComplex f n F) i).trans
      (BoundedFrame.CechPresheafCohomology.homologyIso p k f n F hF i).toLinearEquiv
  have ht := congrArg (fun z => z
    (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
      (BoundedFrame.CechComplex.presheafComplex f n G) i (HomologicalComplex.homologyMap eG i x)))
    (BoundedFrame.CechPresheafRefinement.homology p k f n F G ρ α hF hG i)
  exact (congrArg EF (congrArg (fun z => z x) hs)).trans
    ((congrArg (BoundedFrame.CechPresheafCohomology.homologyIso p k f n F hF i).hom
      (Lifted.HomologyCoordinates.naturality.{u + 1, u + 1, u + 2} R a i
        (HomologicalComplex.homologyMap eG i x)).symm).trans ht)

include ρ α in
theorem cup_eq (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n j) :
    BoundedCrystalline.CechCup.cup p k f n F hF i j x y =
      BoundedCrystalline.CechCup.cup p k f n G hG i j x y := by
  obtain ⟨x, rfl⟩ := (BoundedCrystalline.CechCup.cohomologyEquiv p k f n G hG i).surjective x
  obtain ⟨y, rfl⟩ := (BoundedCrystalline.CechCup.cohomologyEquiv p k f n G hG j).surjective y
  let c := complexMap p k f n F G ρ α
  have hn : HomologicalComplex.homologyMap c (i + j)
      (Cosimplicial.ModuleCup.cohomologyCup _ i j x y) =
        Cosimplicial.ModuleCup.cohomologyCup _ i j
          (HomologicalComplex.homologyMap c i x) (HomologicalComplex.homologyMap c j y) :=
    Cosimplicial.ModuleCup.cohomologyCup_natural (Family.map p k f n F G ρ α) i j x y
  exact (congrArg₂ (fun a b => BoundedCrystalline.CechCup.cup p k f n F hF i j a b)
    (equivalence_natural p k f n F G ρ α hF hG i x).symm
    (equivalence_natural p k f n F G ρ α hF hG j y).symm).trans
      ((BoundedCrystalline.CechCup.cup_comparison p k f n F hF i j
        (HomologicalComplex.homologyMap c i x) (HomologicalComplex.homologyMap c j y)).trans
          ((congrArg (BoundedCrystalline.CechCup.cohomologyEquiv p k f n F hF (i + j)) hn.symm).trans
            ((equivalence_natural p k f n F G ρ α hF hG (i + j)
              (Cosimplicial.ModuleCup.cohomologyCup _ i j x y)).trans
                (BoundedCrystalline.CechCup.cup_comparison p k f n G hG i j x y).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CupFamilyRefinement.Family
