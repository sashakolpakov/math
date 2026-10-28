import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryAffineTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.CoefficientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReducedBaseIso
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Coefficient -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal

/-! The finite-level comparison is transported to the actual p-adic
ordinary de Rham quotient Cech total on the integral coordinate cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "coverOpens" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "coverNerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve coverOpens
local notation "Ip" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "restrict" => ModuleCat.restrictScalars (RingEquiv.toRingHom (WittVector.equiv p))

def coefficients : ModuleCat.{0} ℤ_[p] ⥤ ModuleCat.{2} Rcoeff :=
  restrict ⋙ IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p

instance coefficients_additive : (coefficients p).Additive := by
  dsimp only [coefficients]
  infer_instance

def diagram := OrdinaryAffineTotal.OrdinaryAffineQuotientCech.diagram ℤ_[p] X Ip

def wittIso : ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n ≅
    diagram p X n ⋙ (restrict).mapHomologicalComplex (.up ℕ) :=
  IntegralReducedBaseIso.IntrinsicPadicIntegralReducedBaseIso.iso p X n

def total : CochainComplex (ModuleCat.{0} ℤ_[p]) ℕ :=
  CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.total coverNerve (diagram p X n)

def wittTotalIso : IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X n ≅
    ((restrict).mapHomologicalComplex (.up ℕ)).obj (IntrinsicPadicSmallQuotientTotal.total p X n) :=
  CechAssembly.Iso.CechAssemblyIso.totalIso coverNerve (wittIso p X n) ≪≫
    (CechAssembly.CoefficientTotal.CechAssemblyCoefficientTotal.iso restrict coverNerve
      (CechCone.TotalCoefficient.CechConeTotalCoefficient.finite_indices coverOpens) (diagram p X n)).symm

def coefficientTotalIso : ((coefficients p).mapHomologicalComplex (.up ℕ)).obj (IntrinsicPadicSmallQuotientTotal.total p X n) ≅
    ((IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p).mapHomologicalComplex (.up ℕ)).obj
      (IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.total p X n) :=
  ((IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p).mapHomologicalComplex (.up ℕ)).mapIso
    (wittTotalIso p X n).symm

def fullOpenIso : IntrinsicPadicSmallQuotientTotal.total p X n ≅
    (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X (fun i => (coverOpens i).val) Ip).total (.up ℕ) :=
  OrdinaryAffineTotal.OrdinaryAffineQuotientCech.totalIso ℤ_[p] X coverOpens Ip

def firstThreeHomologyIso : (IntrinsicPadicSmallQuotientTotal.total p X n).homology 1 ≅
    ((IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X (fun i => (coverOpens i).val) Ip).total (.up ℕ)).homology 1 :=
  (HomologicalComplex.homologyFunctor _ _ 1).mapIso (fullOpenIso p X n) ≪≫
    IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X (fun i => (coverOpens i).val) Ip

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def homologyIso :=
  (HomologicalComplex.homologyFunctor _ _ 1).mapIso (coefficientTotalIso p X n) ≪≫
    IntrinsicIntegral.CoefficientTotal.IntrinsicIntegralCoefficientTotal.homologyIso p X Y f hp n J

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientHomology

/-! The actual p-adic to crystalline coefficient transport is exact and
commutes with the original cochain homology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (p : ℕ) [Fact p.Prime]

instance preservesFiniteLimits : PreservesFiniteLimits (IntrinsicPadicSmallQuotientTotal.coefficients p) := by
  dsimp only [IntrinsicPadicSmallQuotientTotal.coefficients, IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients]
  infer_instance

instance preservesFiniteColimits : PreservesFiniteColimits (IntrinsicPadicSmallQuotientTotal.coefficients p) := by
  dsimp only [IntrinsicPadicSmallQuotientTotal.coefficients, IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients]
  infer_instance

instance preservesHomology : (IntrinsicPadicSmallQuotientTotal.coefficients p).PreservesHomology := by
  infer_instance

def iso (K : CochainComplex (ModuleCat.{0} ℤ_[p]) ℕ) (i : ℕ) :
    (((IntrinsicPadicSmallQuotientTotal.coefficients p).mapHomologicalComplex (.up ℕ)).obj K).homology i ≅
      (IntrinsicPadicSmallQuotientTotal.coefficients p).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (IntrinsicPadicSmallQuotientTotal.coefficients p)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientHomology

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent

/-! Descending the actual lifted crystalline coefficient functor back
to p-adic scalars preserves the original module and its maps. -/

open _root_.CategoryTheory

variable (p : ℕ) [Fact p.Prime]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p

def ringEquiv : R ≃+* ℤ_[p] := ULift.ringEquiv.trans (WittVector.equiv p)

def restrict : ModuleCat.{2} R ⥤ ModuleCat.{2} ℤ_[p] :=
  ModuleCat.restrictScalars (IntrinsicPadicCoefficientDescent.ringEquiv p).symm.toRingHom

def equiv (M : ModuleCat.{0} ℤ_[p]) : M ≃ₗ[ℤ_[p]] (IntrinsicPadicCoefficientDescent.restrict p).obj ((F).obj M) where
  toFun x := ⟨⟨x⟩⟩
  invFun x := x.down.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply ULift.ext
    apply ULift.ext
    change a • x = (WittVector.equiv p) ((WittVector.equiv p).symm a) • x
    rw [RingEquiv.apply_symm_apply]

theorem natural {M N : ModuleCat.{0} ℤ_[p]} (a : M ⟶ N) (x : M) :
    IntrinsicPadicCoefficientDescent.equiv p N (a x) = (IntrinsicPadicCoefficientDescent.restrict p).map ((F).map a) (IntrinsicPadicCoefficientDescent.equiv p M x) := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicCoefficientDescent

end

end OAI
