import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.GlobalSections
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechInjectiveResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalComparison

/-! # Cech Sections -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechSections.CrystallineZariskiCechSections

noncomputable section

/-!
# Global Čech descent for the original crystalline resolution

The actual Zariski images of the injective resolution are injective.
Their finite Čech resolutions remain exact after global sections,
by comparison with the trivial injective resolutions. The resulting
total section complex computes the original native derived sections.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {ι : Type u} [Finite ι] (U : ι → X.left.Opens)
  (F : Sheaf (Site.topology p k X) (ModuleCat.{u + 1} (Site.CoefficientRing p k)))
  (I : InjectiveResolution F)

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjectives.CrystallineSheafInjectives.Modules p k
local notation "G" => Sheaf.Γ (Opens.grothendieckTopology X.left) V
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechBicomplex.CrystallineZariskiCechBicomplex.bicomplex p k X U F I
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal.CrystallineZariskiCechTotal.component p k X U F I
local notation "he" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal.CrystallineZariskiCechTotal.vertical p k X U F I
local notation "w" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechTotal.CrystallineZariskiCechTotal.horizontal p k X U F I

local instance coefficientLimits : HasLimitsOfSize.{u, u} V :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

local instance moduleCoproducts : HasCoproducts.{0} V := fun J =>
  (LargeZariski.Colimits.LargeZariskiColimits.modules (Site.CoefficientRing p k)).has_colimits_of_shape (Discrete J)

local instance sheafFiniteBiproducts : HasFiniteBiproducts
    (Sheaf (Opens.grothendieckTopology X.left) V) := Abelian.hasFiniteBiproducts

instance image_injective (q : ℕ) : Injective ((CechBicomplex.CrystallineZariskiCechBicomplex.imageComplex p k X F I).X q) := by
  have : Injective (I.cocomplex.X q) := I.injective q
  change Injective ((Image.CrystallineZariskiImage.functor p k X).obj (I.cocomplex.X q))
  infer_instance

def sectionBicomplex : HomologicalComplex₂ V (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  Comparison.Betti.TotalComplexFunctor.mapBicomplex G K

def sectionTotal : CochainComplex V ℕ :=
  (sectionBicomplex p k X U F I).total (ComplexShape.up ℕ)

def comparison : ((G).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ sectionTotal p k X U F I :=
  Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w

theorem comparison_quasiIso (hU : iSup U = ⊤) : QuasiIso (comparison p k X U F I) := by
  let J (q : ℕ) := LargeZariski.CechInjectiveResolution.LargeZariskiCechInjectiveResolution.resolution
    (Site.CoefficientRing p k) X.left U hU ((A).X q)
  have haug (q : ℕ) :
      (ShortComplex.mk ((G).map (e q)) (((sectionBicomplex p k X U F I).X q).d 0 1)
        (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w q)).Exact ∧
          Mono ((G).map (e q)) :=
    Mapped.InjectiveAugmentation.MappedInjectiveAugmentation.exact_mono (J q) G
  apply Module.TotalComparison.ModuleTotalComparison.quasiIso (Site.CoefficientRing p k)
    (sectionBicomplex p k X U F I) (((G).mapHomologicalComplex (ComplexShape.up ℕ)).obj A)
    (fun q => (G).map (e q)) (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm G K A e he)
    (Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w)
    (fun q => (haug q).1) (fun q => (haug q).2)
  intro q n
  exact Mapped.InjectiveAugmentation.MappedInjectiveAugmentation.exactAt_succ (J q) G n

theorem globalSections_comparison_quasiIso (hU : iSup U = ⊤) :
    QuasiIso (((G).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (CechTotal.CrystallineZariskiCechTotal.comparison p k X U F I)) := by
  have : QuasiIso (Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w) :=
    comparison_quasiIso p k X U F I hU
  have : IsIso (Comparison.Betti.TotalComplexFunctor.totalComparison G K) :=
    (Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G K).isIso_hom
  have h : QuasiIso (Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge G K A e he w ≫
      Comparison.Betti.TotalComplexFunctor.totalComparison G K) := inferInstance
  rw [Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge_comp_totalComparison] at h
  exact h

def homologyIso (hU : iSup U = ⊤) (n : ℕ) :
    (sectionTotal p k X U F I).homology n ≅
      ((Sheaf.Γ (Site.topology p k X) V).rightDerived n).obj F := by
  have : QuasiIso (comparison p k X U F I) := comparison_quasiIso p k X U F I hU
  exact (isoOfQuasiIsoAt (comparison p k X U F I) n).symm ≪≫
    GlobalSections.CrystallineZariskiGlobalSections.homologyIso p k X F I n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineZariski.CechSections.CrystallineZariskiCechSections
