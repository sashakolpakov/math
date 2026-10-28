import OAI.AlgebraicGeometry.Crystalline.Cohomology.SectionLifting
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveFirst
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedEvaluation

/-! # First Derived Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FirstDerivedVanishing.CrystallineFirstDerivedVanishing

noncomputable section

/-!
# First derived-section vanishing for native frame-resolution terms

The first-cycle short exact sequence of the actual injective resolution
has a surjection on sections when the kernel has vanishing first Čech
cohomology. Thus the evaluated resolution is exact in degree one. Applied
to the actual frame-resolution terms, this kills their native first
right-derived evaluation without any additional acyclicity hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (Q : Site.Object p k X)

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

local instance coefficientSmallLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

theorem resolution_exact_one (F : Sheaf J V) (I : InjectiveResolution F)
    (hA : ∀ (t : Finset Q.thickening.ring), Ideal.span (t : Set Q.thickening.ring) = ⊤ →
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).obj F).ExactAt 1) :
    (((LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  change ((I.cocomplex.sc' 0 1 2).map (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro z hz
  obtain ⟨c, hc⟩ := LocalPrimitives.CrystallineLocalPrimitives.cycle_lift p k X (I.cocomplex.sc' 0 1 2) Q z hz
  obtain ⟨y, hy⟩ := SectionLifting.CrystallineSectionLifting.surjective p k X Q
    (InjectiveFirst.InjectiveFirstCycles.shortComplex I) (InjectiveFirst.InjectiveFirstCycles.shortExact I) hA c
  refine ⟨y, ?_⟩
  have hfac := congrArg (fun f => f.hom.app (op Q) y) (I.cocomplex.sc' 0 1 2).toCycles_i
  exact hfac.symm.trans ((congrArg ((I.cocomplex.sc' 0 1 2).iCycles.hom.app (op Q)) hy).trans hc)

theorem isZero (F : Sheaf J V)
    (hA : ∀ (t : Finset Q.thickening.ring), Ideal.span (t : Set Q.thickening.ring) = ⊤ →
      ((CrystallinePrincipal.SheafCech.CrystallinePrincipalSheafCech.functor p k X Q (fun s : t => s.val)).obj F).ExactAt 1) :
    IsZero (DerivedEvaluation.CrystallineDerivedEvaluation.cohomology p k X F Q 1) := by
  let I : InjectiveResolution F := injectiveResolution F
  have hz : IsZero ((((LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex).homology 1) :=
    (resolution_exact_one p k X Q F I hA).isZero_homology
  exact hz.of_iso (I.isoRightDerivedObj (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q) 1)

variable (B σ : Type u) [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

theorem frame_isZero
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (n : ℕ) :
    IsZero (DerivedEvaluation.CrystallineDerivedEvaluation.cohomology p k
      (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
      ((CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X n) Q 1) := by
  apply isZero p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) Q
  intro t ht
  apply CrystallineFrame.SheafCech.CrystallineFrameSheafCech.exactAt p k B σ a Q n (fun s : t => s.val) _ 1 (by decide)
  simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using ht

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FirstDerivedVanishing.CrystallineFirstDerivedVanishing
