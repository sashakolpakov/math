import OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechBicomplex
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechInjectiveResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.TotalComparison

/-! # Zariski Cech Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechSections

noncomputable section

/-!
# IntegralComparison: the finite Čech total complex computes sections of an injective Zariski complex
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechBicomplex

universe u

variable (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})

def sections : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R) ⥤ ModuleCat.{u + 1} R :=
  (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)).obj (op ⊤)

instance sections_additive : (sections R X).Additive where
  map_add := by intros; rfl

variable {ι : Type u} [Finite ι] (U : ι → X.Opens)
  (A : CochainComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u + 1} R)) ℕ)

local instance moduleCoproducts : HasCoproducts.{0} (ModuleCat.{u + 1} R) :=
  fun J => (AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.Colimits.LargeZariskiColimits.modules R).has_colimits_of_shape (Discrete J)

def bicomplex : HomologicalComplex₂ (ModuleCat.{u + 1} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (sections R X) (ZariskiCechBicomplex.bicomplex R X U A)

def total : CochainComplex (ModuleCat.{u + 1} R) ℕ :=
  (bicomplex R X U A).total (ComplexShape.up ℕ)

def comparison : ((sections R X).mapHomologicalComplex (ComplexShape.up ℕ)).obj A ⟶ ZariskiCechSections.total R X U A :=
  AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalEdge (sections R X) (ZariskiCechBicomplex.bicomplex R X U A)
    A (ZariskiCechBicomplex.component R X U A) (ZariskiCechBicomplex.vertical R X U A) (ZariskiCechBicomplex.horizontal R X U A)

theorem comparison_quasiIso (hU : iSup U = ⊤) (hA : ∀ q, Injective (A.X q)) :
    QuasiIso (comparison R X U A) := by
  let (q : ℕ) : Injective (A.X q) := hA q
  let J (q : ℕ) := AlgebraicGeometry.Crystalline.Cohomology.LargeZariski.CechInjectiveResolution.LargeZariskiCechInjectiveResolution.resolution R X U hU (A.X q)
  let K := ZariskiCechBicomplex.bicomplex R X U A
  let G := sections R X
  let e := ZariskiCechBicomplex.component R X U A
  let he := ZariskiCechBicomplex.vertical R X U A
  let w := ZariskiCechBicomplex.horizontal R X U A
  have haug (q : ℕ) :
      (ShortComplex.mk (G.map (e q)) (((bicomplex R X U A).X q).d 0 1)
        (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w q)).Exact ∧ Mono (G.map (e q)) :=
    AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation.MappedInjectiveAugmentation.exact_mono (J q) G
  apply AlgebraicGeometry.Crystalline.Cohomology.Module.TotalComparison.ModuleTotalComparison.quasiIso R (bicomplex R X U A)
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj A) (fun q => G.map (e q))
    (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comm G K A e he)
    (AlgebraicGeometry.Comparison.Betti.TotalComplexEdge.mappedHorizontalAugmentation_comp_d G K A e w)
    (fun q => (haug q).1) (fun q => (haug q).2)
  intro q n
  exact AlgebraicGeometry.Crystalline.Cohomology.Mapped.InjectiveAugmentation.MappedInjectiveAugmentation.exactAt_succ (J q) G n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ZariskiCechSections
