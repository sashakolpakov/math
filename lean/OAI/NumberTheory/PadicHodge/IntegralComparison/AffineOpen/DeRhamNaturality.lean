import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalOpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamRestriction

/-! # De Rham Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamNaturality

noncomputable section

/-! The original native affine-open de Rham comparisons commute on homology with both original restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) {U V : X.left.Opens} (h : V ≤ U)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V)

private abbrev sectionRing (W : X.left.Opens) : CommAlgCat.{u} k :=
  (AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras k X).obj (op W)

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k X) 0))
  (σ τ : Type u) [LinearOrder σ] [LinearOrder τ] [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ k) (sectionRing k X U)]
  [IsScalarTower k (MvPolynomial σ k) (sectionRing k X U)]
  [Algebra.Etale (MvPolynomial σ k) (sectionRing k X U)]
  [Algebra (MvPolynomial τ k) (sectionRing k X V)]
  [IsScalarTower k (MvPolynomial τ k) (sectionRing k X V)]
  [Algebra.Etale (MvPolynomial τ k) (sectionRing k X V)]

theorem chart_homology (i : ℕ) :
    HomologicalComplex.homologyMap
      ((DeRham.Comparison.sectionsMap p k X U hU I σ ≫
        (DeRham.Comparison.sectionIso p k X U hU I).hom) ≫
          Bounded.ChartEvaluationRestriction.map (Witt.Crystalline.wittStructureMap p k X) 0 I h) i =
    HomologicalComplex.homologyMap
      (EtaleZero.ComplexMaps.deRhamMap p k (sectionRing k X U) (sectionRing k X V)
        (SectionRestriction.algHom k X h) ≫
          (DeRham.Comparison.sectionsMap p k X V hV I τ ≫
            (DeRham.Comparison.sectionIso p k X V hV I).hom)) i :=
  let openU : IsOpenImmersion hU.fromSpec := inferInstance
  let openV : IsOpenImmersion hV.fromSpec := inferInstance
  let openG : IsOpenImmersion (Zero.FrameGeometricMap.schemeMap k (sectionRing k X U) (sectionRing k X V)
    (SectionRestriction.algHom k X h)) :=
      SectionRestriction.openImmersion k X h hU hV
  @EtaleZero.GlobalOpenRestriction.homology p inferInstance k (sectionRing k X U) (sectionRing k X V) σ τ
    inferInstance inferInstance inferInstance
    (CommAlgCat.commRing (sectionRing k X U)) (CommAlgCat.commRing (sectionRing k X V))
    (CommAlgCat.algebra (sectionRing k X U)) (CommAlgCat.algebra (sectionRing k X V))
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (SectionRestriction.algHom k X h) openG X.left (Witt.Crystalline.wittStructureMap p k X)
    hU.fromSpec hV.fromSpec openU openV
    (DeRham.Comparison.overWitt p k X U hU)
    (DeRham.Comparison.overWitt p k X V hV)
    (SectionRestriction.factorization k X h hU hV) I U V h
    hU.opensRange_fromSpec hV.opensRange_fromSpec i

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (DeRham.Comparison.map p k X U hU I σ ≫
        Bounded.ChartEvaluationRestriction.map (Witt.Crystalline.wittStructureMap p k X) 0 I h) i =
    HomologicalComplex.homologyMap
      (DeRhamRestriction.map p k X h ≫
        DeRham.Comparison.map p k X V hV I τ) i := by
  let H := HomologicalComplex.homologyFunctor
    (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) (.up ℕ) i
  let c := (DeRham.Comparison.deRhamIso p k X U).hom
  let d := DeRham.Comparison.sectionsMap p k X V hV I τ ≫
    (DeRham.Comparison.sectionIso p k X V hV I).hom
  exact (congrArg H.map (Category.assoc _ _ _)).trans
    ((HomologyMapPrecomposition.equality c _ _ i (chart_homology p k X h hU hV I σ τ i)).trans
      ((congrArg H.map (Category.assoc c _ d).symm).trans
        ((congrArg (fun t => H.map (t ≫ d)) (DeRhamRestriction.chart_naturality p k X h).symm).trans
          (congrArg H.map (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.DeRhamNaturality
