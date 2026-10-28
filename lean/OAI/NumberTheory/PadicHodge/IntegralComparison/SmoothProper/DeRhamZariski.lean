import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ChartSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex

/-! # De Rham Zariski -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamZariski

noncomputable section

/-!
# IntegralComparison: the actual finite smooth proper cover computes the global crystalline Zariski complex by de Rham charts
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

def opens (i : EtaleCover.Index k X) : X.left.Opens := by
  letI : IsOpenImmersion (EtaleCover.chartMap k X i) := EtaleCover.chartMap_open k X i
  exact (EtaleCover.chartMap k X i).opensRange

omit [Fintype k] [CharP k p] in
theorem cover : ⨆ i, opens k X i = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, rfl⟩ := EtaleCover.covers k X x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, rfl⟩

omit [Fintype k] [CharP k p] in
theorem affine (i : EtaleCover.Index k X) : IsAffineOpen (opens k X i) := by
  let : IsOpenImmersion (EtaleCover.chartMap k X i) := EtaleCover.chartMap_open k X i
  exact isAffineOpen_opensRange (EtaleCover.chartMap k X i)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))

def imageIso (i : EtaleCover.Index k X) : BoundedOpen.Resolution.complex (Witt.Crystalline.wittStructureMap p k X) (EtaleCover.chartMap k X i) 0 I ≅
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (opens k X i)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I) := by
  letI : IsOpenImmersion (EtaleCover.chartMap k X i) := EtaleCover.chartMap_open k X i
  exact Bounded.ChartOpenImage.evaluationIso (Witt.Crystalline.wittStructureMap p k X) (EtaleCover.chartMap k X i) 0 I

def map (i : EtaleCover.Index k X) : EtaleZero.DeRham.Comparison.deRhamComplex p k (EtaleCover.coordinateRing k X i) ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (opens k X i)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I) :=
  ChartSections.map p k X I i ≫ (imageIso p k X I i).hom

instance map_quasiIso (i : EtaleCover.Index k X) : QuasiIso (map p k X I i) := by
  dsimp only [map]
  infer_instance

def homologyIso (i : EtaleCover.Index k X) (q : ℕ) :
    (EtaleZero.DeRham.Comparison.deRhamComplex p k (EtaleCover.coordinateRing k X i)).homology q ≅
      (((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) (opens k X i)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I)).homology q :=
  isoOfQuasiIsoAt (map p k X I i) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.DeRhamZariski
