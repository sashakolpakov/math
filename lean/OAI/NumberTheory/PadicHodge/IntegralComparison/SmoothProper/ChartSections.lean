import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleFrames

/-! # Chart Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ChartSections

noncomputable section

/-!
# IntegralComparison: every chart in the actual finite smooth proper cover computes original crystalline sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.EtaleCover OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

@[instance_reducible]
def coordinateOrder (i : EtaleCover.Index k X) : LinearOrder (EtaleCover.coordinateIndex k X i) :=
  LinearOrder.lift' (Fintype.equivFin (EtaleCover.coordinateIndex k X i)) (Fintype.equivFin _).injective

omit [Fintype k] [CharP k p] in
theorem chart_mono (i : EtaleCover.Index k X) : Mono (EtaleCover.chartMap k X i) := by
  let : IsOpenImmersion (EtaleCover.chartMap k X i) := EtaleCover.chartMap_open k X i
  infer_instance

omit [Fintype k] [CharP k p] in
theorem overWitt (i : EtaleCover.Index k X) : EtaleCover.chartMap k X i ≫ Witt.Crystalline.wittStructureMap p k X =
    Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k (EtaleCover.coordinateRing k X i)) := by
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p k →+* k)))
      (EtaleCover.chartMap_over k X i))

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))

def map (i : EtaleCover.Index k X) : EtaleZero.DeRham.Comparison.deRhamComplex p k (EtaleCover.coordinateRing k X i) ⟶
    BoundedOpen.Resolution.complex (Witt.Crystalline.wittStructureMap p k X) (EtaleCover.chartMap k X i) 0 I := by
  exact @EtaleZero.OpenSections.map p inferInstance k (EtaleCover.coordinateRing k X i) (EtaleCover.coordinateIndex k X i)
    inferInstance inferInstance inferInstance inferInstance (EtaleCover.coordinateAlgebra k X i)
    (coordinateOrder k X i) (EtaleCover.coordinateIndex_fintype k X i) (EtaleCover.polynomialAlgebra k X i)
    (EtaleCover.coordinateTower k X i) (EtaleCover.coordinateEtale k X i) X.left (Witt.Crystalline.wittStructureMap p k X)
    (EtaleCover.chartMap k X i) (chart_mono k X i) (overWitt p k X i) I

instance map_quasiIso (i : EtaleCover.Index k X) : QuasiIso (ChartSections.map p k X I i) := by
  exact @EtaleZero.OpenSections.map_quasiIso p inferInstance k (EtaleCover.coordinateRing k X i) (EtaleCover.coordinateIndex k X i)
    inferInstance inferInstance inferInstance inferInstance (EtaleCover.coordinateAlgebra k X i)
    (coordinateOrder k X i) (EtaleCover.coordinateIndex_fintype k X i) (EtaleCover.polynomialAlgebra k X i)
    (EtaleCover.coordinateTower k X i) (EtaleCover.coordinateEtale k X i) X.left (Witt.Crystalline.wittStructureMap p k X)
    (EtaleCover.chartMap k X i) (chart_mono k X i) (overWitt p k X i) I

def homologyIso (i : EtaleCover.Index k X) (q : ℕ) :
    (EtaleZero.DeRham.Comparison.deRhamComplex p k (EtaleCover.coordinateRing k X i)).homology q ≅
      (BoundedOpen.Resolution.complex (Witt.Crystalline.wittStructureMap p k X) (EtaleCover.chartMap k X i) 0 I).homology q :=
  isoOfQuasiIsoAt (ChartSections.map p k X I i) q

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.ChartSections
