import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CupRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.FamilyRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittCechCup

/-! # Witt Geometric Cup -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCup

noncomputable section

/-! The native Witt cochain algebras of two smooth proper schemes map to
the actual common refinement constructed from a genuine scheme morphism.
The refined algebra still computes the original source bounded Ext. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y) (n : ℕ)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "WX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "FX" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.source p k X Y g n

local instance sourceSeparated : IsSeparated WX := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance targetSeparated : IsSeparated (Witt.Crystalline.wittStructureMap p k Y) := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance algebraProducts : HasProducts.{u} (CommAlgCat.{u + 1} R) := by
  have h : HasLimitsOfSize.{u, u} (CommAlgCat.{u + 1} R) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  exact fun I => h.has_limits_of_shape (Discrete I)

abbrev cochainAlgebra := BoundedCrystalline.CechCup.cochainAlgebra WX n FX

def targetMap : WittCechCup.cochainAlgebra p k Y n ⟶ cochainAlgebra p k X Y g n :=
  BoundedCrystalline.CupRefinement.map g.left
    (WittGeometricRefinement.over_witt p k X Y g) n FX (WittFrameFamily.Family.frame p k Y n)
    (WittGeometricRefinement.targetIndex p k X Y g n)
    (WittGeometricRefinement.targetMap p k X Y g n)

def sourceMap : WittCechCup.cochainAlgebra p k X n ⟶ cochainAlgebra p k X Y g n :=
  Cech.FamilyRefinement.Family.map.{u + 1, u} FX (WittFrameFamily.Family.frame p k X n) Sigma.fst
    (WittGeometricRefinement.sourceMap p k X Y g n)
    ((BoundedCrystalline.Site.inclusion WX n).op ⋙ BoundedCrystalline.CechCup.structureAlgebraPresheaf WX)

def equivalence (i : ℕ) :
    (Cosimplicial.ModuleComplex.complex (cochainAlgebra p k X Y g n)).homology i ≃ₗ[R]
      BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) WX n i :=
  BoundedCrystalline.CechCup.cohomologyEquiv p k WX n FX
    (WittGeometricRefinement.covering p k X Y g n) i

theorem targetMap_cup (i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (WittCechCup.cochainAlgebra p k Y n)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (WittCechCup.cochainAlgebra p k Y n)).homology j) :
    HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (targetMap p k X Y g n)) (i + j)
      (Cosimplicial.ModuleCup.cohomologyCup _ i j x y) =
        Cosimplicial.ModuleCup.cohomologyCup _ i j
          (HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (targetMap p k X Y g n)) i x)
          (HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (targetMap p k X Y g n)) j y) :=
  Cosimplicial.ModuleCup.cohomologyCup_natural (targetMap p k X Y g n) i j x y

theorem sourceMap_cup (i j : ℕ)
    (x : (Cosimplicial.ModuleComplex.complex (WittCechCup.cochainAlgebra p k X n)).homology i)
    (y : (Cosimplicial.ModuleComplex.complex (WittCechCup.cochainAlgebra p k X n)).homology j) :
    HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (sourceMap p k X Y g n)) (i + j)
      (Cosimplicial.ModuleCup.cohomologyCup _ i j x y) =
        Cosimplicial.ModuleCup.cohomologyCup _ i j
          (HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (sourceMap p k X Y g n)) i x)
          (HomologicalComplex.homologyMap (Cosimplicial.ModuleCup.complexMap (sourceMap p k X Y g n)) j y) :=
  Cosimplicial.ModuleCup.cohomologyCup_natural (sourceMap p k X Y g n) i j x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCup
