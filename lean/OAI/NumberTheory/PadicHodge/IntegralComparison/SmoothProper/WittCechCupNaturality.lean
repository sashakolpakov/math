import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCup

/-! # Witt Cech Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCupNaturality

noncomputable section

/-! The actual bounded crystalline restriction maps preserve the native
frame cup product, through the original Čech-to-Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
  WittCechCup

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CechCup.forgetModule (B := WittVector p k)

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} R) := by
  let h : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
  exact fun I => h.has_limits_of_shape (Discrete I)

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

abbrev nativeComparison (n : ℕ) :=
  BoundedCrystalline.CechCup.comparison f n (WittFrameFamily.Family.frame p k X n)

theorem comparison_f (n a : ℕ) : (nativeComparison p k X n).hom.f a =
    piComparison T (fun t : Fin (a + 1) → StandardCover.Index k X =>
      (WittCechCup.algebraSections p k X n).obj
        (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))) := by
  let P := fun t : Fin (a + 1) → StandardCover.Index k X =>
    (WittCechCup.algebraSections p k X n).obj
      (op (Presentation.TupleProducts.family.{u + 1, u} (WittFrameFamily.Family.frame p k X n) a t))
  let C := NonemptyCechNerve.complexFunctor (A := ModuleCat.{u + 1} R) (WittFrameFamily.Family.frame p k X n)
  change piComparison T P ≫
    (C.map (𝟙 (WittCechTransitionData.sections p k X n))).f a = piComparison T P
  exact (congrArg (fun z => piComparison T P ≫ z.f a) (C.map_id (WittCechTransitionData.sections p k X n))).trans (Category.comp_id _)

variable (n m : ℕ) (hnm : n ≤ m)

abbrev complexMap := Cosimplicial.ModuleCup.complexMap (WittCechCup.transition p k X n m hnm)

theorem complexes : complexMap p k X n m hnm ≫ (nativeComparison p k X n).hom =
    (nativeComparison p k X m).hom ≫ WittCechTransition.map p k X n m hnm := by
  apply HomologicalComplex.Hom.ext
  funext a
  exact (congrArg (fun z => (complexMap p k X n m hnm).f a ≫ z) (comparison_f p k X n a)).trans
    ((AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.piComparison_map T (WittCechCup.coefficient p k X n m hnm a)).trans
      (congrArg (fun z => z ≫ (WittCechTransition.map p k X n m hnm).f a)
        (comparison_f p k X m a)).symm)

local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.map (p := p) (J := PIdeal) (δ := DP) f n m hnm

theorem equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (WittCechCup.cochainAlgebra p k X m)).homology i) :
    WittCechCup.equivalence p k X n i (HomologicalComplex.homologyMap (complexMap p k X n m hnm) i x) =
      g i (WittCechCup.equivalence p k X m i x) := by
  let c := complexMap p k X n m hnm
  let eₙ := (nativeComparison p k X n).hom
  let eₘ := (nativeComparison p k X m).hom
  let a := WittCechTransition.map p k X n m hnm
  have hs : HomologicalComplex.homologyMap c i ≫ HomologicalComplex.homologyMap eₙ i =
      HomologicalComplex.homologyMap eₘ i ≫ HomologicalComplex.homologyMap a i :=
    (HomologicalComplex.homologyMap_comp c eₙ i).symm.trans
      ((congrArg (fun z => HomologicalComplex.homologyMap z i) (complexes p k X n m hnm)).trans
        (HomologicalComplex.homologyMap_comp eₘ a i))
  let E := (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
    (WittCechTransitionData.complex p k X n) i).trans
      (WittCechCohomology.homologyIso p k X n i).toLinearEquiv
  exact (congrArg E (congrArg (fun z => z x) hs)).trans
    (WittCechLinearNaturality.transport p k X n m hnm i
      (HomologicalComplex.homologyMap eₘ i x))

theorem cup_natural (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f m i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f m j) :
    g (i + j) (WittCechCup.cup p k X m i j x y) = WittCechCup.cup p k X n i j (g i x) (g j y) := by
  obtain ⟨x, rfl⟩ := (WittCechCup.equivalence p k X m i).surjective x
  obtain ⟨y, rfl⟩ := (WittCechCup.equivalence p k X m j).surjective y
  rw [WittCechCup.cup_comparison, ← equivalence_natural p k X n m hnm,
    Cosimplicial.ModuleCup.cohomologyCup_natural]
  rw [← equivalence_natural p k X n m hnm i x,
    ← equivalence_natural p k X n m hnm j y, WittCechCup.cup_comparison]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCupNaturality
