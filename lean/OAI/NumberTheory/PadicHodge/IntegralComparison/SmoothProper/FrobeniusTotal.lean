import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusCoherence
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.TotalFiniteness
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.ScalarRestriction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Frobenius Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusTotal

noncomputable section

/-! Finite cohomology of the actual affine Čech total complex of the Frobenius de Rham modules. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable (k : Type u) [Field k] [Fintype k]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

def bicomplex : HomologicalComplex₂ (ModuleCat.{u} Γ(Spec (CommRingCat.of k), ⊤)) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseCechComplexFunctor X.hom (FrobeniusCharts.opens k X)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (Frobenius.DeRhamGlobal.complex k X)

def total : CochainComplex (ModuleCat.{u} Γ(Spec (CommRingCat.of k), ⊤)) ℕ :=
  (bicomplex k X).total (.up ℕ)

theorem row_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n q : ℕ) :
    Module.Finite Γ(Spec (CommRingCat.of k), ⊤) (((bicomplex k X).X n).homology q) := by
  let : (FrobeniusCoherence.term k X n).IsQuasicoherent :=
    FrobeniusCoherence.quasicoherent k X n
  let : (FrobeniusCoherence.term k X n).IsFiniteType :=
    FrobeniusCoherence.finiteType k X n
  exact Projective.CechFiniteness.finite k X.hom hprojective
    (FrobeniusCoherence.term k X n) (FrobeniusCharts.opens k X)
    (IsOpenCover.mk (FrobeniusCharts.cover k X))
    (FrobeniusCharts.affine k X) q

theorem finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite Γ(Spec (CommRingCat.of k), ⊤) ((FrobeniusTotal.total k X).homology n) := by
  let : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) := isNoetherianRing_of_ringEquiv k
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  exact IntegralComparison.Module.TotalFiniteness.finite (bicomplex k X) n (fun q p _ => row_finite k X hprojective q p)

def coefficientFunctor : ModuleCat.{u} Γ(Spec (CommRingCat.of k), ⊤) ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

instance coefficient_additive : (coefficientFunctor k).Additive := by
  dsimp only [coefficientFunctor]
  infer_instance

instance coefficient_preservesFiniteLimits : PreservesFiniteLimits (coefficientFunctor k) where
  preservesFiniteLimits T _ _ := by
    dsimp only [coefficientFunctor]
    infer_instance

instance coefficient_preservesFiniteColimits : PreservesFiniteColimits (coefficientFunctor k) where
  preservesFiniteColimits T _ _ := by
    dsimp only [coefficientFunctor]
    infer_instance

instance coefficient_preservesHomology : (coefficientFunctor k).PreservesHomology := by infer_instance

def coefficientTotal : CochainComplex (ModuleCat.{u} k) ℕ :=
  ((coefficientFunctor k).mapHomologicalComplex (ComplexShape.up ℕ)).obj (FrobeniusTotal.total k X)

def coefficientHomologyIso (n : ℕ) :
    (coefficientTotal k X).homology n ≅ (coefficientFunctor k).obj ((FrobeniusTotal.total k X).homology n) :=
  ((FrobeniusTotal.total k X).sc n).mapHomologyIso (coefficientFunctor k)

theorem coefficient_finite (hprojective : Projectivity.Construction.ProjectiveOver k X.hom) (n : ℕ) :
    Module.Finite k ((coefficientTotal k X).homology n) := by
  let : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) ((FrobeniusTotal.total k X).homology n) := finite k X hprojective n
  have hf : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
  let : Module.Finite k ((coefficientFunctor k).obj ((FrobeniusTotal.total k X).homology n)) :=
    IntegralComparison.Finite.ScalarRestriction.finite _ hf ((FrobeniusTotal.total k X).homology n)
  exact Module.Finite.equiv (coefficientHomologyIso k X n).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.FrobeniusTotal
