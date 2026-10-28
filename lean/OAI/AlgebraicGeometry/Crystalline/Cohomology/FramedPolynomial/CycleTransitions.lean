import OAI.AlgebraicGeometry.Crystalline.Cohomology.Framed.TowerSectionLifting

/-! # Cycle Transitions -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.CycleTransitions.FramedPolynomialCycleTransitions

noncomputable section

/-!
# Surjective tower transitions for the cycles of a structure-sheaf resolution

The initial cycle sheaf is the original structure sheaf. Each later
cycle section lifts to the preceding injective term by native Čech
acyclicity, extends along the tower by injectivity, and projects back
to a cycle. Thus every cycle sheaf has surjective tower transitions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff)

local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "O" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.structureSheaf p k X
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Topology.FramedCrystallineTopology.native p k B σ (fun i => r (MvPolynomial.X i))
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.Tower.FramedPolynomialTower.tower p k B σ r hr hbase
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ (fun i => r (MvPolynomial.X i)) V
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Framed.TowerSectionLifting.FramedTowerSectionLifting.nativeDiagram p k B σ r hr hbase

variable (I : InjectiveResolution (Site.structureSheaf p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)))

theorem surjective (j n : ℕ) : Function.Surjective
    (SequentialLimit.SequentialLimitLifting.transition (Site.CoefficientRing p k)
      ((D).obj (InjectiveCycle.InjectiveCycleTower.cycle I j)) n) := by
  cases j with
  | zero =>
    have : Epi (((D).obj O).map (homOfLE (Nat.le_succ n)).op) :=
      (ModuleCat.epi_iff_surjective _).mpr
        (TowerSurjectivity.FramedPolynomialTowerSurjectivity.structure_surjective p k B σ r hr hbase (Nat.le_succ n))
    apply (ModuleCat.epi_iff_surjective _).mp
    rw [← NatIso.naturality_1 ((D).mapIso (InjectiveCycle.InjectiveCycleTower.augmentationIso I))
      (homOfLE (Nat.le_succ n)).op]
    infer_instance
  | succ j =>
    intro c
    have hA := DerivedVanishing.CrystallineDerivedVanishing.cycles_acyclic p k X O
      (EmptyFrame.CrystallineEmptyFrame.structure_acyclic p k B) I j
    obtain ⟨y, hy⟩ := SectionLifting.CrystallineSectionLifting.surjective p k X ((T).obj n).base
      (InjectiveCycle.InjectiveCycleTower.shortComplex I j) (InjectiveCycle.InjectiveCycleTower.shortExact I j)
        (fun t ht => hA _ t ht 1 (by decide)) c
    let F : Sheaf K V := (U).obj (I.cocomplex.X j)
    have : Injective F := by
      dsimp [F]
      infer_instance
    obtain ⟨y', hy'⟩ := TowerSurjectivity.FramedPolynomialTowerSurjectivity.injective_surjective
      p k B σ r hr hbase F (Nat.le_succ n) y
    refine ⟨(InjectiveCycle.InjectiveCycleTower.projection I j).hom.app (op ((T).obj (n + 1)).base) y', ?_⟩
    have hc := ConcreteCategory.congr_hom
      ((InjectiveCycle.InjectiveCycleTower.projection I j).hom.naturality
        (((T).map (homOfLE (Nat.le_succ n))).hom).op) y'
    exact hc.symm.trans ((congrArg
      ((InjectiveCycle.InjectiveCycleTower.projection I j).hom.app (op ((T).obj n).base)) hy').trans hy)

include hr hbase in
theorem global_projection_epi (j : ℕ) :
    Epi ((Framed.TowerSectionLifting.FramedTowerSectionLifting.nativeGlobal p k B σ r).map (InjectiveCycle.InjectiveCycleTower.projection I j)) :=
  Framed.TowerSectionLifting.FramedTowerSectionLifting.global_epi p k B σ r hr hbase
    (InjectiveCycle.InjectiveCycleTower.shortComplex I j) (InjectiveCycle.InjectiveCycleTower.shortExact I j)
    (DerivedVanishing.CrystallineDerivedVanishing.cycles_acyclic p k X O
      (EmptyFrame.CrystallineEmptyFrame.structure_acyclic p k B) I j)
    (surjective p k B σ r hr hbase I j)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.CycleTransitions.FramedPolynomialCycleTransitions
