import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.InjectiveSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.ToGlobalResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.DeRham

/-! # Global Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalSections

noncomputable section

/-!
# IntegralComparison: actual chart de Rham sections compute a restricted global crystalline injective resolution
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (g : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) [Mono g]
  (hg : g ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg 0 I
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0

def map : BoundedEtale.ZeroCohomology.Comparison.complex p k C ⟶
    InjectiveSectionCohomology.complex R A IX :=
  Acyclic.InjectiveSections.map R A (Bounded.RelativeSheafComplex.complex f 0 F) IX
    (ToGlobalResolution.map p k C σ g hg I)

instance map_quasiIso : QuasiIso (map p k C σ g hg I) := by
  let : QuasiIso (Bounded.RelativeSheafComplex.augmentation f 0 F) :=
    BoundedEtale.ZeroResolution.augmentation_quasiIso p k C σ
  exact Acyclic.InjectiveSections.quasiIso R A (Bounded.RelativeSheafComplex.complex f 0 F)
    (Bounded.RelativeSheafComplex.augmentation f 0 F) IX
    (ToGlobalResolution.map p k C σ g hg I)
    (ToGlobalResolution.augmentation p k C σ g hg I)
    (fun n q => BoundedEtale.ZeroAcyclicTerms.positive_cohomology_zero p k C σ n q)

def sectionIso : InjectiveSectionCohomology.complex R A IX ≅
    Bounded.GeometricResolution.complex g hg 0 I :=
  Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f 0) (IX).cocomplex

def presheafMap : BoundedEtale.ZeroCohomology.Comparison.complex p k C ⟶
    Bounded.GeometricResolution.complex g hg 0 I :=
  map p k C σ g hg I ≫ (sectionIso p k C g hg I).hom

instance presheafMap_quasiIso : QuasiIso (presheafMap p k C σ g hg I) := by
  dsimp only [presheafMap]
  infer_instance

def deRhamMap : DeRham.Comparison.deRhamComplex p k C ⟶
    Bounded.GeometricResolution.complex g hg 0 I :=
  (DeRham.Comparison.frameIso p k C).inv ≫
    (BoundedEtale.ZeroFrameDeRhamIso.complexIso p k C σ).hom ≫ presheafMap p k C σ g hg I

instance deRhamMap_quasiIso : QuasiIso (deRhamMap p k C σ g hg I) := by
  dsimp only [deRhamMap]
  infer_instance

def homologyIso (i : ℕ) : (DeRham.Comparison.deRhamComplex p k C).homology i ≅
    (Bounded.GeometricResolution.complex g hg 0 I).homology i :=
  isoOfQuasiIsoAt (deRhamMap p k C σ g hg I) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalSections
