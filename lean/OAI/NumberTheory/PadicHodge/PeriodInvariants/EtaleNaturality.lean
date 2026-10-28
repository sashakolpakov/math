import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleIsoCompatibility
import OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois
import OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricNaturality

/-! # Etale Naturality -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleNaturality

noncomputable section

/-!
# Galois-equivariant pullback for actual integral models

Every morphism of models induces pullback on geometric rational etale
cohomology. The scheme-level naturality square, the proved pullback
composition law, and agreement with the existing isomorphism action
show that this map intertwines the actual local Galois representations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricNaturality OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars
open OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCoherence OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleIsoCompatibility
open OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {M N P : IntegralGeometry.IntegralModel p K}

def geometricMap (g : M ⟶ N) : GeometricGenericFiber.EtaleGalois.geometricGenericFiber p K M ⟶ GeometricGenericFiber.EtaleGalois.geometricGenericFiber p K N :=
  (IntegralGeometry.genericFiberFunctor p K ⋙ GeometricNaturality.geometricFiberFunctor K (AlgebraicClosure K)).map g

def etalePullback (g : M ⟶ N) (n : ℕ) :
    EtaleGalois.geometricEtaleCohomology p K N n →ₗ[ℚ_[p]] EtaleGalois.geometricEtaleCohomology p K M n :=
  BigEtaleCohomology.pullbackQp p (geometricMap p K g) n

theorem etalePullback_equivariant (g : M ⟶ N) (n : ℕ) (σ : CrystallineScalars.LocalGalois K)
    (x : EtaleGalois.geometricEtaleCohomology p K N n) :
    etalePullback p K g n (EtaleGalois.etaleRepresentation p K N n σ x) =
      EtaleGalois.etaleRepresentation p K M n σ (etalePullback p K g n x) := by
  let eM := IntegralComparison.Frobenius.Geometry.geometricFiberIso ((IntegralGeometry.genericFiberFunctor p K).obj M).hom σ
  let eN := IntegralComparison.Frobenius.Geometry.geometricFiberIso ((IntegralGeometry.genericFiberFunctor p K).obj N).hom σ
  have hn : geometricMap p K g ≫ eN.hom = eM.hom ≫ geometricMap p K g :=
    GeometricNaturality.geometricFiberIso_natural K (AlgebraicClosure K) σ ((IntegralGeometry.genericFiberFunctor p K).map g)
  change BigEtaleCohomology.pullback p (geometricMap p K g) n (IntegralComparison.Etale.Frobenius.cohomologyPullback p eN n x) =
    IntegralComparison.Etale.Frobenius.cohomologyPullback p eM n (BigEtaleCohomology.pullback p (geometricMap p K g) n x)
  rw [← EtaleIsoCompatibility.pullback_iso, ← EtaleIsoCompatibility.pullback_iso, BigEtaleCoherence.pullback_comp, hn, ← BigEtaleCoherence.pullback_comp]

def etaleIntertwining (g : M ⟶ N) (n : ℕ) :
    Representation.IntertwiningMap (EtaleGalois.etaleRepresentation p K N n) (EtaleGalois.etaleRepresentation p K M n) :=
  (etalePullback p K g n).intertwiningMap_of_isIntertwiningMap _ _
    (etalePullback_equivariant p K g n)

theorem etalePullback_id (M : IntegralGeometry.IntegralModel p K) (n : ℕ) (x : EtaleGalois.geometricEtaleCohomology p K M n) :
    etalePullback p K (𝟙 M) n x = x := by
  change BigEtaleCohomology.pullback p (geometricMap p K (𝟙 M)) n x = x
  change BigEtaleCohomology.pullback p ((IntegralGeometry.genericFiberFunctor p K ⋙ GeometricNaturality.geometricFiberFunctor K (AlgebraicClosure K)).map (𝟙 M)) n x = x
  rw [CategoryTheory.Functor.map_id]
  exact BigEtaleCoherence.pullback_id p _ n x

theorem etalePullback_comp (g : M ⟶ N) (h : N ⟶ P) (n : ℕ)
    (x : EtaleGalois.geometricEtaleCohomology p K P n) :
    etalePullback p K g n (etalePullback p K h n x) = etalePullback p K (g ≫ h) n x := by
  change BigEtaleCohomology.pullback p (geometricMap p K g) n (BigEtaleCohomology.pullback p (geometricMap p K h) n x) =
    BigEtaleCohomology.pullback p (geometricMap p K (g ≫ h)) n x
  have hc : geometricMap p K (g ≫ h) = geometricMap p K g ≫ geometricMap p K h :=
    (IntegralGeometry.genericFiberFunctor p K ⋙ GeometricNaturality.geometricFiberFunctor K (AlgebraicClosure K)).map_comp g h
  rw [hc, BigEtaleCoherence.pullback_comp]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleNaturality
