import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCechLevel
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCupNaturality

/-! # Witt Cup Level -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupLevel

noncomputable section

/-! The actual bounded crystalline restriction maps preserve the native
frame cup product, through the original Čech-to-Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.StandardCover
  SmoothProperWittCup

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

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCupNaturality (nativeComparison complexMap complexes)

variable (n m : ℕ) (hnm : n ≤ m)

local notation "g" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition.map (p := p) (J := PIdeal) (δ := DP) f n m hnm

private theorem algebra_homology (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (SmoothProper.WittCechCup.cochainAlgebra p k X m)).homology i) :
    HomologicalComplex.homologyMap (SmoothProper.WittCechCupNaturality.nativeComparison p k X n).hom i
      (HomologicalComplex.homologyMap (SmoothProper.WittCechCupNaturality.complexMap p k X n m hnm) i x) =
        HomologicalComplex.homologyMap (SmoothProper.WittCechTransition.map p k X n m hnm) i
          (HomologicalComplex.homologyMap (SmoothProper.WittCechCupNaturality.nativeComparison p k X m).hom i x) := by
  let c := SmoothProper.WittCechCupNaturality.complexMap p k X n m hnm
  let eₙ := (SmoothProper.WittCechCupNaturality.nativeComparison p k X n).hom
  let eₘ := (SmoothProper.WittCechCupNaturality.nativeComparison p k X m).hom
  let a := SmoothProper.WittCechTransition.map p k X n m hnm
  have hs := (HomologicalComplex.homologyMap_comp c eₙ i).symm.trans
    ((congrArg (fun z => HomologicalComplex.homologyMap z i) (SmoothProper.WittCechCupNaturality.complexes p k X n m hnm)).trans
      (HomologicalComplex.homologyMap_comp eₘ a i))
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hs) x

abbrev equivalence_natural (i : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (SmoothProper.WittCechCup.cochainAlgebra p k X m)).homology i) :=
  let c := SmoothProper.WittCechCupNaturality.complexMap p k X n m hnm
  let eₘ := (SmoothProper.WittCechCupNaturality.nativeComparison p k X m).hom
  let E := (Lifted.HomologyCoordinates.equivalence.{u + 1, u + 1, u + 2} R
    (SmoothProper.WittCechTransitionData.complex p k X n) i).trans
      (SmoothProperWittCup.homologyIso p k X n i).toLinearEquiv
  (BalancedBounded.CechCup.cohomologyEquiv_apply p k f n (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n) i (HomologicalComplex.homologyMap c i x)).trans
      ((congrArg E (algebra_homology p k X n m hnm i x)).trans
        ((WittCechLevel.transport p k X n m hnm i
          (HomologicalComplex.homologyMap eₘ i x)).trans
            (congrArg (g i)
              (BalancedBounded.CechCup.cohomologyEquiv_apply p k f m (SmoothProper.WittFrameFamily.Family.frame p k X m)
                (SmoothProper.WittFrameCover.covering p k X m) i x).symm)))

theorem cup_natural (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f m i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f m j) :
    g (i + j) (SmoothProperWittCup.cup p k X m i j x y) = SmoothProperWittCup.cup p k X n i j (g i x) (g j y) := by
  obtain ⟨x, rfl⟩ := (SmoothProperWittCup.equivalence p k X m i).surjective x
  obtain ⟨y, rfl⟩ := (SmoothProperWittCup.equivalence p k X m j).surjective y
  rw [SmoothProperWittCup.cup_comparison, ← equivalence_natural p k X n m hnm,
    Cosimplicial.ModuleCup.cohomologyCup_natural]
  rw [← equivalence_natural p k X n m hnm i x,
    ← equivalence_natural p k X n m hnm j y, SmoothProperWittCup.cup_comparison]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupLevel
