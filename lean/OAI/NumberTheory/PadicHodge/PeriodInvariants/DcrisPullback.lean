import OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisMem
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleNaturality

/-! # Dcris Pullback -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisPullback

noncomputable section

/-!
# Pullback on actual crystalline invariants

The proved Galois-equivariant etale pullback induces a map on D_cris by
tensoring with the actual period ring and restricting to fixed vectors.
Thus the endomorphism maps in the comparison statement are independently
constructed from the geometric morphisms.
-/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients OAI.NumberTheory.PadicHodge.PeriodInvariants.Embedding.Period OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
open OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisMem OAI.NumberTheory.PadicHodge.PeriodInvariants.Mem.Construction OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleNaturality

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

local instance periodQpSMul : SMul ℚ_[p] (PeriodRing.Bcris p) := DcrisMem.periodQpSMul p
local instance periodQpModule : Module ℚ_[p] (PeriodRing.Bcris p) := DcrisMem.periodQpModule p
local instance periodQpMulAction : MulAction ℚ_[p] (PeriodRing.Bcris p) := DcrisMem.periodQpMulAction p
local instance periodK0Module : Module (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) := DcrisMem.periodK0Module p K

section Representations

variable {V W : Type*} [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]

local instance tensorK0Module : Module (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p ⊗[ℚ_[p]] V) := TensorProduct.leftModule

variable {ρ : Representation ℚ_[p] (CrystallineScalars.LocalGalois K) V} {τ : Representation ℚ_[p] (CrystallineScalars.LocalGalois K) W}

local instance invariantModule (ρ : Representation ℚ_[p] (CrystallineScalars.LocalGalois K) V) :
    Module (ResidueCoefficients.K0 p K) (DcrisMem.Dcris p K ρ) := Submodule.module (DcrisMem.Dcris p K ρ)

def map (f : Representation.IntertwiningMap ρ τ) : DcrisMem.Dcris p K ρ →ₗ[ResidueCoefficients.K0 p K] DcrisMem.Dcris p K τ :=
  Mem.Construction.periodMap (R := ℚ_[p]) (K0 := ResidueCoefficients.K0 p K) (B := PeriodRing.Bcris p) (Embedding.Period.localPeriodActionOverK0 p K) f

theorem map_coe (f : Representation.IntertwiningMap ρ τ) (x : DcrisMem.Dcris p K ρ) :
    (map p K f x : PeriodRing.Bcris p ⊗[ℚ_[p]] W) = f.toLinearMap.baseChange (PeriodRing.Bcris p) x := rfl

end Representations

variable {M N : IntegralGeometry.IntegralModel p K}

local instance geometricInvariantModule (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :
    Module (ResidueCoefficients.K0 p K) (DcrisMem.geometricDcris p K M n) := Submodule.module (DcrisMem.geometricDcris p K M n)

def geometricPullback (g : M ⟶ N) (n : ℕ) :
    DcrisMem.geometricDcris p K N n →ₗ[ResidueCoefficients.K0 p K] DcrisMem.geometricDcris p K M n :=
  map p K (EtaleNaturality.etaleIntertwining p K g n)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisPullback
