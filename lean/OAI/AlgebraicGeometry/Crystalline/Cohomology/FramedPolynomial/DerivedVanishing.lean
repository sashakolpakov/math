import OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.CycleTransitions

/-! # Derived Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.DerivedVanishing.FramedPolynomialDerivedVanishing

noncomputable section

/-!
# Positive derived global vanishing for the framed structure sheaf

The cycle sequences of the original native injective resolution remain
exact after framed global sections: native Čech acyclicity gives exactness
at every envelope level, and surjective cycle transitions lift compatible
sections. Restriction preserves injectives, so this computes the actual
right-derived global sections of the original framed structure sheaf.
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
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.Category.FramedCrystallineCategory.Object p k B σ (fun i => r (MvPolynomial.X i))
local notation "U" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedCrystalline.SheafExactness.FramedCrystallineSheafExactness.restriction p k B σ (fun i => r (MvPolynomial.X i)) V
local notation "G" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Framed.TowerSectionLifting.FramedTowerSectionLifting.nativeGlobal p k B σ r

local instance : HasLimitsOfShape Cᵒᵖ V := ModuleCat.hasLimitsOfShape

variable (I : InjectiveResolution (Site.structureSheaf p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)))

theorem cycle_lift (j : ℕ) (x : (G).obj (I.cocomplex.X j))
    (hx : (G).map (I.cocomplex.d j (j + 1)) x = 0) :
    ∃ c : (G).obj (InjectiveCycle.InjectiveCycleTower.cycle I j),
      (G).map (InjectiveCycle.InjectiveCycleTower.inclusion I j) c = x := by
  let S := ShortComplex.mk (InjectiveCycle.InjectiveCycleTower.inclusion I j) (I.cocomplex.d j (j + 1))
    (kernel.condition (I.cocomplex.d j (j + 1)))
  have hS : S.Exact := ShortComplex.kernelSequence_exact (I.cocomplex.d j (j + 1))
  have : Mono S.f := by change Mono (kernel.ι (I.cocomplex.d j (j + 1))); infer_instance
  have he := hS.map_of_mono_of_preservesKernel G inferInstance inferInstance
  exact (ShortComplex.moduleCat_exact_iff (S.map G)).mp he x hx

include hr hbase in
theorem exactAt (n : ℕ) :
    (((G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change ((I.cocomplex.sc' n (n + 1) (n + 2)).map G).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨c, hc⟩ := cycle_lift p k B σ r I (n + 1) x hx
  have : Epi ((G).map (InjectiveCycle.InjectiveCycleTower.projection I n)) :=
    CycleTransitions.FramedPolynomialCycleTransitions.global_projection_epi p k B σ r hr hbase I n
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp this c
  refine ⟨y, ?_⟩
  have hf := congrArg (fun f => (G).map f) (InjectiveCycle.InjectiveCycleTower.projection_inclusion I n)
  rw [Functor.map_comp] at hf
  have he := ConcreteCategory.congr_hom hf y
  exact he.symm.trans ((congrArg ((G).map (InjectiveCycle.InjectiveCycleTower.inclusion I (n + 1))) hy).trans hc)

include hr hbase in
theorem isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero (((Sheaf.Γ K V).rightDerived n).obj
      (StructureSections.FramedPolynomialStructureSections.structureSheaf p k B σ r)) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    let I : InjectiveResolution O := injectiveResolution O
    let I' : InjectiveResolution ((U).obj O) := ExactInjective.ExactInjectiveResolution.map U I
    have he : (((Sheaf.Γ K V).mapHomologicalComplex (ComplexShape.up ℕ)).obj I'.cocomplex).ExactAt (n + 1) :=
      exactAt p k B σ r hr hbase I n
    exact he.isZero_homology.of_iso (I'.isoRightDerivedObj (Sheaf.Γ K V) (n + 1))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FramedPolynomial.DerivedVanishing.FramedPolynomialDerivedVanishing
