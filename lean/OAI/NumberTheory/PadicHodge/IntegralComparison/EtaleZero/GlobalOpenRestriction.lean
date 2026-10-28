import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.OpenEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartSectionSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SectionSquare

/-! # Global Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalOpenRestriction

noncomputable section

/-! Original affine open comparisons respect the actual Zariski restriction on global crystalline sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C D σ τ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [CommRing D] [Algebra k C] [Algebra k D]
  [LinearOrder σ] [LinearOrder τ] [Fintype σ] [Fintype τ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  [Algebra (MvPolynomial τ k) D] [IsScalarTower k (MvPolynomial τ k) D] [Algebra.Etale (MvPolynomial τ k) D]
  (a : C →ₐ[k] D) [IsOpenImmersion (Zero.FrameGeometricMap.schemeMap k C D a)]
  {Y : Scheme.{u}} {fY : Y ⟶ Spec (CommRingCat.of (WittVector p k))}
  (c : (Crystalline.Presentation.affineScheme k C).left ⟶ Y) (d : (Crystalline.Presentation.affineScheme k D).left ⟶ Y)
  [IsOpenImmersion c] [IsOpenImmersion d]
  (hC : c ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C))
  (hD : d ≫ fY = Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k D))
  (e : Zero.FrameGeometricMap.schemeMap k C D a ≫ c = d)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p k)})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) fY 0))
  {U V : Y.Opens} (hVU : V ≤ U) (eU : c.opensRange = U) (eV : d.opensRange = V)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "IC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution c hC 0 I
local notation "ID" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution d hD 0 I

include e in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      ((OpenSections.map p k C σ c hC I ≫
        (Bounded.ChartEvaluationCoordinates.iso fY c 0 U eU I).hom) ≫
          Bounded.ChartEvaluationRestriction.map fY 0 I hVU) i =
    HomologicalComplex.homologyMap
      (ComplexMaps.deRhamMap p k C D a ≫
        (OpenSections.map p k D τ d hD I ≫
          (Bounded.ChartEvaluationCoordinates.iso fY d 0 V eV I).hom)) i := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u + 2} R) (.up ℕ) i
  let v := (Bounded.GeometricOpenSections.complexIso d hD 0 I).inv ≫
    (Bounded.ChartEvaluationCoordinates.iso fY d 0 V eV I).hom
  have h := Functor.SectionSquare.square H
    (ResolutionSections.map p k C σ IC)
    (ComplexMaps.deRhamMap p k C D a)
    (ResolutionSections.map p k D τ ID) _
    ((Bounded.GeometricOpenSections.complexIso c hC 0 I).inv ≫
      (Bounded.ChartEvaluationCoordinates.iso fY c 0 U eU I).hom)
    v (Bounded.ChartEvaluationRestriction.map fY 0 I hVU)
    (GlobalRestriction.homology p k C D σ τ a c d hC hD e I i)
    ((Bounded.ChartSectionSquare.square (Zero.FrameGeometricMap.schemeMap k C D a) c d
      (Zero.FrameGeometricMap.overWitt p k C D a) hC hD e 0 I hVU eU eV).trans
        ((congrArg (fun t => GeometricSections.restriction p k C D a IC ≫ t)
          (Category.assoc _ _ v).symm).trans (Category.assoc _ _ v).symm))
  exact (congrArg (fun t => H.map (t ≫ Bounded.ChartEvaluationRestriction.map fY 0 I hVU))
    (OpenEvaluation.factorization p k C σ c hC I U eU)).trans
      (h.trans
        ((congrArg H.map (Category.assoc (ComplexMaps.deRhamMap p k C D a)
          (ResolutionSections.map p k D τ ID) v)).trans
            (congrArg (fun t => H.map (ComplexMaps.deRhamMap p k C D a ≫ t))
              (OpenEvaluation.factorization p k D τ d hD I V eV).symm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.GlobalOpenRestriction
