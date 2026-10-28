import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois

/-! # Comparison Scalars -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars

noncomputable section

/-! Canonical scalar structures for the full de Rham comparison. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonBd OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonGalois OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois.PeriodStructure OAI.NumberTheory.PadicHodge.WeakAdmissibility.Galois
variable (p : ℕ) [Fact p.Prime]

def padicToBdRPlus : ℚ_[p] →+* Logarithm.PeriodRings.BdRPlus p :=
  (DeRham.bInfToBdRPlus p).comp (PeriodInvariants.Nontriviality.padicToBinf p)

def padicToBdR : ℚ_[p] →+* Logarithm.PeriodRings.BdR p := (ComparisonBd.bdRPlusToBdR p).comp (padicToBdRPlus p)

theorem padicToBdRPlus_integer (a : ℤ_[p]) :
    padicToBdRPlus p (algebraMap ℤ_[p] ℚ_[p] a) =
      DeRham.bInfToBdRPlus p (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (Logarithm.PeriodRings.padicIntToAInf p a)) := by
  unfold padicToBdRPlus PeriodInvariants.Nontriviality.padicToBinf
  rw [RingHom.comp_apply, IsLocalization.lift_eq]
  rfl

theorem aCrisToBdRPlus_padicInt (a : ℤ_[p]) :
    Comparison.aCrisToBdRPlus p (Cyclotomic.padicIntToACris p a) = padicToBdRPlus p (algebraMap ℤ_[p] ℚ_[p] a) := by
  rw [padicToBdRPlus_integer]
  change Comparison.aCrisToBdRPlus p
    (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)
      (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.padicIntToAInf p a))) = _
  rw [Comparison.aCrisToBdRPlus_of, DeRhamEnvelope.uncompletedToBdRPlus_algebraMap]

theorem bCrisPlusToBdRPlus_padic (a : ℚ_[p]) :
    Comparison.bCrisPlusToBdRPlus p (Galois.PeriodStructure.padicToPositive p a) = padicToBdRPlus p a := by
  have he : (Comparison.bCrisPlusToBdRPlus p).comp (Galois.PeriodStructure.padicToPositive p) = padicToBdRPlus p := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro b
    change Comparison.bCrisPlusToBdRPlus p (Galois.PeriodStructure.padicToPositive p (algebraMap ℤ_[p] ℚ_[p] b)) =
      padicToBdRPlus p (algebraMap ℤ_[p] ℚ_[p] b)
    rw [Galois.PeriodStructure.padicToPositive_int]
    change Comparison.bCrisPlusToBdRPlus p (algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Cyclotomic.padicIntToACris p b)) = _
    rw [Comparison.bCrisPlusToBdRPlus_algebraMap, aCrisToBdRPlus_padicInt]
  exact DFunLike.congr_fun he a

theorem bCrisToBdR_padic (a : ℚ_[p]) : ComparisonBd.bCrisToBdR p (Galois.PeriodStructure.padicToBCris p a) = padicToBdR p a := by
  rw [Galois.PeriodStructure.padicToBCris, RingHom.comp_apply, ComparisonBd.bCrisToBdR_algebraMap]
  change ComparisonBd.bdRPlusToBdR p (Comparison.bCrisPlusToBdRPlus p (Galois.PeriodStructure.padicToPositive p a)) =
    ComparisonBd.bdRPlusToBdR p (padicToBdRPlus p a)
  rw [bCrisPlusToBdRPlus_padic]

instance deRham_padicAlgebra : Algebra ℚ_[p] (Logarithm.PeriodRings.BdR p) := (padicToBdR p).toAlgebra

instance deRham_padicModule : Module ℚ_[p] (Logarithm.PeriodRings.BdR p) := Algebra.toModule

def bCrisToBdRAlg : Logarithm.PeriodRings.BCris p →ₐ[ℚ_[p]] Logarithm.PeriodRings.BdR p :=
  { ComparisonBd.bCrisToBdR p with commutes' := bCrisToBdR_padic p }

theorem galoisBdRAction_padic (σ : PeriodInvariants.PeriodRing.PadicGalois p) (a : ℚ_[p]) :
    ComparisonGalois.galoisBdRAction p σ (padicToBdR p a) = padicToBdR p a := by
  rw [← bCrisToBdR_padic, ← ComparisonGalois.bCrisToBdR_galois, Galois.PeriodStructure.galoisBCrisMap_padic]

def galoisBdRAlgEquiv (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Logarithm.PeriodRings.BdR p ≃ₐ[ℚ_[p]] Logarithm.PeriodRings.BdR p :=
  { ComparisonGalois.galoisBdRAction p σ with commutes' := galoisBdRAction_padic p σ }

def deRhamRepresentation : Representation ℚ_[p] (PeriodInvariants.PeriodRing.PadicGalois p) (Logarithm.PeriodRings.BdR p) where
  toFun σ := (galoisBdRAlgEquiv p σ).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change ComparisonGalois.galoisBdRAction p 1 x = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    change ComparisonGalois.galoisBdRAction p (σ * τ) x = ComparisonGalois.galoisBdRAction p σ (ComparisonGalois.galoisBdRAction p τ x)
    rw [map_mul]
    rfl

theorem comparison_linear_galois (σ : PeriodInvariants.PeriodRing.PadicGalois p) (x : Logarithm.PeriodRings.BCris p) :
    (bCrisToBdRAlg p).toLinearMap (Galois.PeriodStructure.periodRepresentation p σ x) =
      deRhamRepresentation p σ ((bCrisToBdRAlg p).toLinearMap x) :=
  ComparisonGalois.bCrisToBdR_galois p σ x

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ComparisonScalars
