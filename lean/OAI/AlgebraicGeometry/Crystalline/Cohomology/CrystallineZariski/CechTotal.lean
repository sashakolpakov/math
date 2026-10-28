import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Large.SheafTotalComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SingleAugmentation

/-! # Cech Total -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal.CrystallineZariskiCechTotal

noncomputable section

/-!
# Total Čech descent for the original crystalline resolution

The canonical map from the actual Zariski image of an injective
crystalline resolution to its Čech total complex is a quasi-isomorphism.
The row exactness assumptions of the general total-complex theorem
are discharged by the proved native Čech augmentation.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {ι : Type u} (U : ι → X.left.Opens)
  (F : Sheaf (Site.topology p k X) (ModuleCat.{u + 1} (Site.CoefficientRing p k)))
  (I : InjectiveResolution F)

def component (q : ℕ) : (CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I).X q ⟶
    ((CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I).X q).X 0 :=
  ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q).f 0

theorem vertical (q r : ℕ) (_h : (ComplexShape.up ℕ).Rel q r) :
    component p k X U F I q ≫ ((CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I).d q r).f 0 =
      (CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I).d q r ≫ component p k X U F I r := by
  exact congrArg (fun f => f.f 0) ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).comm q r)

theorem horizontal (q : ℕ) : component p k X U F I q ≫
    ((CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I).X q).d 0 1 = 0 :=
  ((CochainComplex.fromSingle₀Equiv _ _)
    ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q)).property

def total := (CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I).total (ComplexShape.up ℕ)

def comparison : CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I ⟶ CrystallineZariskiCechTotal.total p k X U F I :=
  (SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge (CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I))
    (CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I) (component p k X U F I)
    (vertical p k X U F I) (horizontal p k X U F I)

theorem comparison_quasiIso (hU : iSup U = ⊤) : QuasiIso (comparison p k X U F I) := by
  have hq (q : ℕ) : QuasiIso ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q) :=
    CechBicomplex.CrystallineZariskiCechBicomplex.row_quasiIso p k X U F I hU q
  have haug (q : ℕ) :
      (ShortComplex.mk (component p k X U F I q)
        (((CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I).X q).d 0 1)
        (horizontal p k X U F I q)).Exact ∧ Mono (component p k X U F I q) := by
    exact SingleAugmentation.SingleAugmentationExact.exact_mono _ _
      ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q)
      ((hq q).quasiIsoAt 0) (horizontal p k X U F I q)
  apply Large.SheafTotalComparison.LargeSheafTotalComparison.quasiIso (Site.CoefficientRing p k) X.left
    (CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I)
    (CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I) (component p k X U F I)
    (vertical p k X U F I) (horizontal p k X U F I)
    (fun q => (haug q).1) (fun q => (haug q).2)
  intro q n
  have : QuasiIsoAt ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q) (n + 1) :=
    (hq q).quasiIsoAt (n + 1)
  exact (exactAt_iff_of_quasiIsoAt
    ((CechBicomplex.CrystallineZariskiCechBicomplex.augmentation p k X U F I).f q) (n + 1)).mp
      (CochainComplex.exactAt_succ_single_obj _ n)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal.CrystallineZariskiCechTotal
