import OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedSectionDifferential
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialComparison

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison

noncomputable section

/-!
# Original affine crystalline cohomology and completed PD de Rham forms

The proved section equivalence in each degree respects the original
differentials and the prescribed coefficient lifts. It identifies the
actual affine crystalline section complex with the actual completed
PD de Rham complex, and hence computes the original crystalline Ext.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]
  (r : MvPolynomial σ (WittVector p k) →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) (MvPolynomial σ (WittVector p k))) =
    (algebraMap k B).comp WittVector.constantCoeff) [Fintype σ] [LinearOrder σ]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "Poly" => MvPolynomial σ W
local notation "a" => fun i => r (MvPolynomial.X i)
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "KS" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution.CrystallineFrameSheafResolution.complex p k B σ a
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialSheafResolution.CrystallinePolynomialSheafResolution.coefficientLift p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.complex p k B σ r hr hbase
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.EnvelopeFrames.AffineEnvelopeFrames.tower p k B Poly r hr hbase
local notation "Completed" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.PolynomialOperators.AffinePolynomialOperators.derivative p k B σ r hr hbase
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LiftedTermLimit.CrystallineLiftedTermLimit.sectionsEquiv p k B σ r hr hbase
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryComplex p k B σ r

abbrev largeLift : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 2} R := ModuleCat.uliftFunctor.{u + 2, u + 1} R

local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison.largeLift p k

def tensorComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((L).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((E).mapHomologicalComplex (ComplexShape.up ℕ)).obj T)

def completedComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((L).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (((E).mapHomologicalComplex (ComplexShape.up ℕ)).obj (PD.PDDeRham.complex p k B Tower))

def componentIso (n : ℕ) : (S).X n ≅ (tensorComplex p k B σ r hr hbase).X n :=
  (L).mapIso (e n).toModuleIso

omit [LinearOrder σ] in
theorem tensor_d (n : ℕ) : (T).d n (n + 1) =
    CrystallineFrame.SectionDifferential.CrystallineFrameSectionDifferential.differentialMap p k B σ r hr hbase n :=
  CochainComplex.of_d (fun j => ModuleCat.of W (Koszul.Tensor.KoszulTensor.Term W σ Completed j))
    (fun j => ModuleCat.ofHom (Koszul.Tensor.KoszulTensor.differential W σ Completed D j)) n

def tensorIso : S ≅ tensorComplex p k B σ r hr hbase :=
  HomologicalComplex.Hom.isoOfComponents (componentIso p k B σ r hr hbase) (by
    intro n m h
    have hm : n + 1 = m := h
    subst m
    change (L).map (ModuleCat.ofHom (e n).toLinearMap) ≫ (L).map ((E).map ((T).d n (n + 1))) =
      (L).map (ModuleCat.ofHom (Linear.rightComp R _ (((KS).d n (n + 1)).hom))) ≫
        (L).map (ModuleCat.ofHom (e (n + 1)).toLinearMap)
    rw [tensor_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    exact (LiftedSectionDifferential.CrystallineLiftedSectionDifferential.sectionsEquiv_differential p k B σ r hr hbase n x.down).symm)

def complexIso : S ≅ completedComplex p k B σ r hr hbase :=
  tensorIso p k B σ r hr hbase ≪≫
    ((L).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
      (((E).mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
        (PolynomialComparison.AffinePolynomialComparison.complexIso p k B σ r hr hbase))

def homologyIso (n : ℕ) : (completedComplex p k B σ r hr hbase).homology n ≅
    ModuleCat.of R (Site.integralCohomology p k X n) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (complexIso p k B σ r hr hbase).symm ≪≫
    CrystallineFrame.SectionComparison.CrystallineFrameSectionComparison.ordinaryHomologyIso p k B σ r hr hbase n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Comparison.AffineCrystallineComparison
