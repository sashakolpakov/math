import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.DeRhamCoefficientComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartOpenImage

/-! # De Rham -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRham.Comparison

noncomputable section

/-!
# IntegralComparison: native de Rham sections compare with the original resolution on étale affine opens
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) (U : X.left.Opens) (hU : IsAffineOpen U)

private abbrev sectionRing : CommAlgCat.{u} k := (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op U)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRham.Comparison.sectionRing k X U

def deRhamIso :
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Global.DeRhamCoefficientComplex.complex p k X) ≅
        EtaleZero.DeRham.Comparison.deRhamComplex p k C :=
  Global.DeRhamCoefficientComplex.evaluationIso p k X U

omit [Fintype k] [CharP k p] in
theorem overWitt : hU.fromSpec ≫ Witt.Crystalline.wittStructureMap p k X = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C) :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (WittVector.constantCoeff : WittVector p k →+* k)))
      (SectionBase.overBase k X U hU))

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))

def sectionIso : BoundedOpen.Resolution.complex (Witt.Crystalline.wittStructureMap p k X) hU.fromSpec 0 I ≅
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I) :=
  Bounded.ChartOpenImage.evaluationIso (Witt.Crystalline.wittStructureMap p k X) hU.fromSpec 0 I ≪≫
    eqToIso (congrArg (fun V =>
      ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) V).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I))
          hU.opensRange_fromSpec)

variable (σ : Type u) [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) (sectionRing k X U)]
  [IsScalarTower k (MvPolynomial σ k) (sectionRing k X U)]
  [Algebra.Etale (MvPolynomial σ k) (sectionRing k X U)]

def sectionsMap : EtaleZero.DeRham.Comparison.deRhamComplex p k C ⟶
    BoundedOpen.Resolution.complex (Witt.Crystalline.wittStructureMap p k X) hU.fromSpec 0 I := by
  have hmono : Mono hU.fromSpec := inferInstance
  exact @EtaleZero.OpenSections.map p inferInstance k C σ
    inferInstance inferInstance inferInstance (CommAlgCat.commRing C) (CommAlgCat.algebra C)
    inferInstance inferInstance inferInstance inferInstance inferInstance X.left (Witt.Crystalline.wittStructureMap p k X)
    hU.fromSpec hmono (overWitt p k X U hU) I

instance sectionsMap_quasiIso : QuasiIso (sectionsMap p k X U hU I σ) := by
  have hmono : Mono hU.fromSpec := inferInstance
  exact @EtaleZero.OpenSections.map_quasiIso p inferInstance k C σ
    inferInstance inferInstance inferInstance (CommAlgCat.commRing C) (CommAlgCat.algebra C)
    inferInstance inferInstance inferInstance inferInstance inferInstance X.left (Witt.Crystalline.wittStructureMap p k X)
    hU.fromSpec hmono (overWitt p k X U hU) I

def map :
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Global.DeRhamCoefficientComplex.complex p k X) ⟶
    ((BoundedOpen.SectionComplex.evaluation (B := WittVector p k) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (BoundedOpen.SectionComplex.complex (Witt.Crystalline.wittStructureMap p k X) 0 I) :=
  (deRhamIso p k X U).hom ≫
    sectionsMap p k X U hU I σ ≫ (sectionIso p k X U hU I).hom

instance map_quasiIso : QuasiIso (Comparison.map p k X U hU I σ) := by
  dsimp only [Comparison.map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRham.Comparison
