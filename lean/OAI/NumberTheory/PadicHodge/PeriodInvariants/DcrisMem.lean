import OAI.NumberTheory.PadicHodge.PeriodInvariants.Mem
import OAI.NumberTheory.PadicHodge.PeriodInvariants.Embedding
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois

/-! # Dcris Mem -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisMem

noncomputable section

/-!
# Actual D_cris over the constructed unramified field K_0

The coefficient action is the proved embedding W(k)[1/p] into B_cris. The
diagonal Galois action defines D_cris, and actual period Frobenius restricts
semilinearly to it. No dimension, admissibility, or comparison assertion is
assumed in these constructions.
-/

open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Mem.Construction OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients
  Embedding.Period

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

local instance periodQpSMul : SMul ℚ_[p] (PeriodRing.Bcris p) := (PeriodRing.bcris_padicAlgebra p).toSMul

local instance periodQpModule : Module ℚ_[p] (PeriodRing.Bcris p) :=
  (inferInstance : Algebra ℚ_[p] (PeriodRing.Bcris p)).toModule

local instance periodQpMulAction : MulAction ℚ_[p] (PeriodRing.Bcris p) := (periodQpModule p).toMulAction

local instance periodK0Module : Module (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p) :=
  (inferInstance : Algebra (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p)).toModule

theorem frobenius_action (σ : CrystallineScalars.LocalGalois K) (b : PeriodRing.Bcris p) :
    CrystallineScalars.bcrisFrobeniusAlg p (Embedding.Period.localPeriodActionOverK0 p K σ b) =
      Embedding.Period.localPeriodActionOverK0 p K σ (CrystallineScalars.bcrisFrobeniusAlg p b) := by
  change CrystallineScalars.bcrisFrobeniusAlg p (CrystallineScalars.localPeriodAction p K σ b) =
    CrystallineScalars.localPeriodAction p K σ (CrystallineScalars.bcrisFrobeniusAlg p b)
  exact (CrystallineScalars.localPeriodAction_frobenius p K σ b).symm

section Representation

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local instance tensorK0Module : Module (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p ⊗[ℚ_[p]] V) := TensorProduct.leftModule

variable (ρ : Representation ℚ_[p] (CrystallineScalars.LocalGalois K) V)

def tensorRepresentation : Representation (ResidueCoefficients.K0 p K) (CrystallineScalars.LocalGalois K) (PeriodRing.Bcris p ⊗[ℚ_[p]] V) :=
  Mem.Construction.periodRepresentation (R := ℚ_[p]) (K0 := ResidueCoefficients.K0 p K) (B := PeriodRing.Bcris p) (Embedding.Period.localPeriodActionOverK0 p K) ρ

def Dcris : Submodule (ResidueCoefficients.K0 p K) (PeriodRing.Bcris p ⊗[ℚ_[p]] V) :=
  Mem.Construction.periodInvariants (R := ℚ_[p]) (K0 := ResidueCoefficients.K0 p K) (B := PeriodRing.Bcris p) (Embedding.Period.localPeriodActionOverK0 p K) ρ

local instance dcrisModule : Module (ResidueCoefficients.K0 p K) (Dcris p K ρ) := Submodule.module (Dcris p K ρ)

theorem mem_Dcris (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) :
    x ∈ Dcris p K ρ ↔ ∀ σ, tensorRepresentation p K ρ σ x = x := Iff.rfl

def tensorFrobenius :
    PeriodRing.Bcris p ⊗[ℚ_[p]] V →ₛₗ[(ResidueCoefficients.coefficientFrobenius p K).toRingHom] PeriodRing.Bcris p ⊗[ℚ_[p]] V :=
  Mem.Construction.periodOperator (R := ℚ_[p]) (K0 := ResidueCoefficients.K0 p K) (B := PeriodRing.Bcris p)
    (ResidueCoefficients.coefficientFrobenius p K).toRingHom (CrystallineScalars.bcrisFrobeniusAlg p) (Embedding.Period.bcrisFrobenius_k0_smul p K)

theorem tensorFrobenius_commutes (σ : CrystallineScalars.LocalGalois K) (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) :
    tensorFrobenius p K (tensorRepresentation p K ρ σ x) =
      tensorRepresentation p K ρ σ (tensorFrobenius p K x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    change CrystallineScalars.bcrisFrobeniusAlg p (Embedding.Period.localPeriodActionOverK0 p K σ b) ⊗ₜ[ℚ_[p]] ρ σ v =
      Embedding.Period.localPeriodActionOverK0 p K σ (CrystallineScalars.bcrisFrobeniusAlg p b) ⊗ₜ[ℚ_[p]] ρ σ v
    exact congrArg (fun c => c ⊗ₜ[ℚ_[p]] ρ σ v) (frobenius_action p K σ b)
  | add x y hx hy => simp only [map_add, hx, hy]

def dcrisFrobenius : Dcris p K ρ →ₛₗ[(ResidueCoefficients.coefficientFrobenius p K).toRingHom] Dcris p K ρ :=
  (tensorFrobenius p K).restrict (fun x hx σ => by
    change tensorRepresentation p K ρ σ (tensorFrobenius p K x) = tensorFrobenius p K x
    exact (tensorFrobenius_commutes p K ρ σ x).symm.trans
      (congrArg (tensorFrobenius p K) (hx σ)))

/-- The canonical scalar-extension map associated with actual crystalline invariants. -/
def scalarExtension : PeriodRing.Bcris p ⊗[ResidueCoefficients.K0 p K] Dcris p K ρ →ₗ[PeriodRing.Bcris p] PeriodRing.Bcris p ⊗[ℚ_[p]] V :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b =>
        { toFun := fun x => b • (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V)
          map_add' := fun x y => smul_add b (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) y
          map_smul' := fun c x => smul_comm b c (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) }
      map_add' := by
        intro b c
        apply LinearMap.ext
        intro x
        exact add_smul b c (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V)
      map_smul' := by
        intro b c
        apply LinearMap.ext
        intro x
        exact mul_smul b c (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) }

theorem scalarExtension_tmul (b : PeriodRing.Bcris p) (x : Dcris p K ρ) :
    scalarExtension p K ρ (b ⊗ₜ[ResidueCoefficients.K0 p K] x) = b • (x : PeriodRing.Bcris p ⊗[ℚ_[p]] V) := rfl

end Representation

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois

abbrev geometricDcris (M : IntegralGeometry.IntegralModel p K) (n : ℕ) := Dcris p K (EtaleGalois.etaleRepresentation p K M n)

local instance geometricDcrisModule (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :
    Module (ResidueCoefficients.K0 p K) (geometricDcris p K M n) := Submodule.module (geometricDcris p K M n)

def geometricDcrisFrobenius (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :
    geometricDcris p K M n →ₛₗ[(ResidueCoefficients.coefficientFrobenius p K).toRingHom] geometricDcris p K M n :=
  dcrisFrobenius p K (EtaleGalois.etaleRepresentation p K M n)

def geometricScalarExtension (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :
    PeriodRing.Bcris p ⊗[ResidueCoefficients.K0 p K] geometricDcris p K M n →ₗ[PeriodRing.Bcris p]
      PeriodRing.Bcris p ⊗[ℚ_[p]] EtaleGalois.geometricEtaleCohomology p K M n :=
  scalarExtension p K (EtaleGalois.etaleRepresentation p K M n)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.DcrisMem
