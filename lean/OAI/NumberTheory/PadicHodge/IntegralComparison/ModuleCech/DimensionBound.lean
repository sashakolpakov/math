import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison
import OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing

/-! # Dimension Bound -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.DimensionBound

noncomputable section

/-! The original coefficient Čech complex of a quasicoherent module
obeys the topological dimension bound on an affine open cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (R : Type u) [CommRing R]
  (X : Over (Spec (CommRingCat.of R))) (M : X.left.Modules)
  {ι : Type u} (U : ι → X.left.Opens)

def complex : CochainComplex (ModuleCat.{u} R) ℕ :=
  (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).obj
    ((Affine.HomologyPresheaf.functor R X).obj M)

def forgetIso :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomologicalComplex (.up ℕ)).obj
        (complex R X M U) ≅
      (cechComplexFunctor U).obj M.presheaf :=
  AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    (FormalCoproduct.mk ι U).cech ((Affine.HomologyPresheaf.functor R X).obj M)

variable [X.left.IsSeparated] [M.IsQuasicoherent]
  (hU : ⨆ i, U i = ⊤) (haffine : ∀ i, IsAffineOpen (U i))

def cohomologyIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj ((complex R X M U).homology (n + 1)) ≅
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X.left (n + 1)).obj M :=
  (((complex R X M U).sc (n + 1)).mapHomologyIso
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.homologyMapIso (forgetIso R X M U) (n + 1) ≪≫
      AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.CechComparison.IntrinsicCech.quasicoherent_affineCover_cechCohomologyIso M U hU haffine n

include hU haffine in
theorem vanishing [NoetherianSpace X.left] (g : ℕ)
    (hdim : topologicalKrullDim X.left ≤ (g : WithBot ℕ∞)) (n : ℕ) (hn : g < n) :
    Subsingleton ((complex R X M U).homology n) := by
  cases n with
  | zero => omega
  | succ n =>
      let : NoetherianSpace X.left.toTopCat := inferInstanceAs (NoetherianSpace X.left)
      let F := (SheafOfModules.toSheaf X.left.ringCatSheaf).obj M
      have hlt : topologicalKrullDim X.left < (n + 1 : WithBot ℕ∞) :=
        lt_of_le_of_lt hdim (by exact_mod_cast hn)
      let : Subsingleton ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.Cohomology.ZariskiCohomology.zariskiFunctor X.left (n + 1)).obj M) :=
        AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing.Projective.GrothendieckVanishing X.left.toTopCat (n + 1) hlt F
      exact (cohomologyIso R X M U hU haffine n).addCommGroupIsoToAddEquiv.injective.subsingleton

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ModuleCech.DimensionBound
