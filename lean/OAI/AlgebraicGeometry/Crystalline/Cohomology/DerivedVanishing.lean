import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineCech.CechAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.InjectiveCycle
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedEvaluation

/-! # Derived Vanishing -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedVanishing.CrystallineDerivedVanishing

noncomputable section

/-!
# All positive derived-section vanishing for native frame terms

Starting from a Čech-acyclic sheaf, the short exact cycle sequences of its
actual injective resolution remain Čech-acyclic. Section lifting makes
every evaluated positive-degree cycle a boundary. Consequently all
positive right-derived evaluations vanish. The actual frame-resolution
terms satisfy the criterion by their proved principal Čech exactness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k

theorem cycles_acyclic (F : Sheaf J V) (hF : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X F)
    (I : InjectiveResolution F) (n : ℕ) :
    CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X (InjectiveCycle.InjectiveCycleTower.cycle I n) := by
  induction n with
  | zero => exact CrystallineCech.CechAcyclic.CrystallineCechAcyclic.of_iso p k X hF (InjectiveCycle.InjectiveCycleTower.augmentationIso I)
  | succ n ih =>
    exact CrystallineCech.CechAcyclic.CrystallineCechAcyclic.cokernel p k X
      (InjectiveCycle.InjectiveCycleTower.shortComplex I n) (InjectiveCycle.InjectiveCycleTower.shortExact I n) ih

theorem cycle_section_lift (F : Sheaf J V) (I : InjectiveResolution F) (n : ℕ)
    (Q : Site.Object p k X) (x : (I.cocomplex.X n).obj.obj (op Q))
    (hx : (I.cocomplex.d n (n + 1)).hom.app (op Q) x = 0) :
    ∃ c : (InjectiveCycle.InjectiveCycleTower.cycle I n).obj.obj (op Q),
      (InjectiveCycle.InjectiveCycleTower.inclusion I n).hom.app (op Q) c = x := by
  let K := ShortComplex.mk (InjectiveCycle.InjectiveCycleTower.inclusion I n) (I.cocomplex.d n (n + 1))
    (kernel.condition (I.cocomplex.d n (n + 1)))
  have hK : K.Exact := ShortComplex.kernelSequence_exact (I.cocomplex.d n (n + 1))
  have : Mono K.f := by change Mono (kernel.ι (I.cocomplex.d n (n + 1))); infer_instance
  have he := hK.map_of_mono_of_preservesKernel (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q)
    inferInstance inferInstance
  exact (ShortComplex.moduleCat_exact_iff (K.map (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q))).mp he x hx

theorem evaluated_exactAt (F : Sheaf J V) (hF : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X F)
    (I : InjectiveResolution F) (Q : Site.Object p k X) (n : ℕ) :
    (((LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  change ((I.cocomplex.sc' n (n + 1) (n + 2)).map (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q)).Exact
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨c, hc⟩ := cycle_section_lift p k X F I (n + 1) Q x hx
  have hA := cycles_acyclic p k X F hF I n
  obtain ⟨y, hy⟩ := SectionLifting.CrystallineSectionLifting.surjective p k X Q
    (InjectiveCycle.InjectiveCycleTower.shortComplex I n) (InjectiveCycle.InjectiveCycleTower.shortExact I n)
      (fun t ht => hA Q t ht 1 (by decide)) c
  refine ⟨y, ?_⟩
  have hfac := congrArg (fun f => f.hom.app (op Q) y) (InjectiveCycle.InjectiveCycleTower.projection_inclusion I n)
  exact hfac.symm.trans
    ((congrArg ((InjectiveCycle.InjectiveCycleTower.inclusion I (n + 1)).hom.app (op Q)) hy).trans hc)

theorem isZero (F : Sheaf J V) (hF : CrystallineCech.CechAcyclic.CrystallineCechAcyclic.Acyclic p k X F)
    (Q : Site.Object p k X) (n : ℕ) (hn : n ≠ 0) :
    IsZero (DerivedEvaluation.CrystallineDerivedEvaluation.cohomology p k X F Q n) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n =>
    let I : InjectiveResolution F := injectiveResolution F
    have hz := (evaluated_exactAt p k X F hF I Q n).isZero_homology
    exact hz.of_iso (I.isoRightDerivedObj (LocalPrimitives.CrystallineLocalPrimitives.evaluation p k X Q) (n + 1))

variable (B σ : Type u) [CommRing B] [Algebra k B] (a : σ → B) [Fintype σ]

theorem frame_isZero
    (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B))
    (i n : ℕ) (hn : n ≠ 0) :
    IsZero (DerivedEvaluation.CrystallineDerivedEvaluation.cohomology p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)
      ((CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a).X i) Q n) :=
  isZero p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B) _
    (CrystallineCech.CechAcyclic.CrystallineCechAcyclic.frame p k B σ a i) Q n hn

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.DerivedVanishing.CrystallineDerivedVanishing
