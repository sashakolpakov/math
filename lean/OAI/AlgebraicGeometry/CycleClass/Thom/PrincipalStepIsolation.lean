import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.QuotientPrimeModule

/-! # Principal Step Isolation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions.ResidualStalkPrime

/-! Each residual prime is the actual stalk kernel of its original
cycle support, with the corresponding restricted quotient module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientPoints.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.QuotientPrimeModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem quotientSupport_kernelPrime (X : Scheme) (D : IrreducibleCloseds X)
    (x : X) (hxD : x ∈ (D : Set X)) (q : Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD))) :
    StalkPrimeQuotient.Constructions.kernelPrime X (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport X D x hxD q) x (SupportQuotientPoints.Constructions.point_mem_quotientSupport X D x hxD q) =
      PrimeSpectrum.comap (algebraMap (X.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing X D x hxD)) q := by
  apply (X.fromSpecStalk x).isEmbedding.injective
  rw [StalkPrimeQuotient.Constructions.kernelPrime_image]
  exact (StalkPrimeQuotient.Constructions.SupportScheme.supportPoint_quotientSupport X D x hxD q).trans
    (congrArg (fun f => f q) (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupportMap_ambient X D x hxD))

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier))
  (r : V.carrier.presheaf.stalk x) (hn : IsSMulRegular (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) r)

local notation "R" => V.carrier.presheaf.stalk x
local notation "P" => PrimeSpectrum.asIdeal (OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD)
local notation "A" => R ⧸ Ideal.span (Singleton.singleton r : Set R)
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions.residualCycleSupport V D x hxD r hn

theorem residual_kernelPrime (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    StalkPrimeQuotient.Constructions.kernelPrime V.carrier (F t).val x
      (SupportQuotientPoints.Constructions.point_mem_quotientSupport V.carrier D.val x hxD (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)) =
    PrimeSpectrum.comap (algebraMap R A) t.val :=
  (quotientSupport_kernelPrime V.carrier D.val x hxD (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)).trans
    (ResidualSourceEquiv.Constructions.residualSourcePrime_comap R P r t)

def residualQuotientIso (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A (A ⧸ t.val.asIdeal)) ≅
      ModuleCat.of R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier (F t).val x
        (SupportQuotientPoints.Constructions.point_mem_quotientSupport V.carrier D.val x hxD (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t))) :=
  QuotientPrimeModule.Constructions.restrictedQuotientIso R A Ideal.Quotient.mk_surjective t.val.asIdeal ≪≫
    (Submodule.quotEquivOfEq _ _ (congrArg PrimeSpectrum.asIdeal
      (residual_kernelPrime V D x hxD r hn t)).symm).toModuleIso

end AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions.ResidualStalkPrime

namespace AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions

/-! The exact original residual support kernel contains the parent
kernel and the cut equation. Thus the genuine isolated intersection
condition passes to the remaining equations in the original ambient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions.ResidualStalkPrime
open OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0)
  (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier)) (hxB : x ∈ B)

local notation "R" => V.carrier.presheaf.stalk x
local notation "P" => PrimeSpectrum.asIdeal (OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD)
local notation "Q" => OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD
local notation "r" => V.carrier.presheaf.germ B x hxB (B.topIso.hom s)

theorem step_kernel_contains (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hxC : x ∈ (C.val : Set V.carrier)) (hC : Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C ≠ 0) :
    P ≤ (StalkPrimeQuotient.Constructions.kernelPrime V.carrier C.val x hxC).asIdeal ∧ r ∈ (StalkPrimeQuotient.Constructions.kernelPrime V.carrier C.val x hxC).asIdeal := by
  obtain ⟨t, ht⟩ := ResidualEquiv.Constructions.exists_residualCycleSupport V D B s hs x hxD hxB C hxC hC
  subst C
  let hn := ReferenceSectionEulerStep.Constructions.Reference.sectionQuotientRegular V D B s hs x hxD hxB
  have hk := congrArg PrimeSpectrum.asIdeal (ResidualStalkPrime.residual_kernelPrime V D x hxD r hn t)
  have hq := congrArg PrimeSpectrum.asIdeal (ResidualSourceEquiv.Constructions.residualSourcePrime_comap R P r t)
  constructor
  · rw [hk, ← hq]
    intro a ha
    change algebraMap R Q a ∈ (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t).asIdeal
    have hz : algebraMap R Q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    rw [hz]
    exact (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t).asIdeal.zero_mem
  · rw [hk]
    change algebraMap R (R ⧸ Ideal.span {r}) r ∈ t.val.asIdeal
    have hz : algebraMap R (R ⧸ Ideal.span {r}) r = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hz]
    exact t.val.asIdeal.zero_mem

theorem principalStep_isolated_tail (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hxC : x ∈ (C.val : Set V.carrier)) (hC : Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C ≠ 0)
    (rs : List R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R Q ⊆
      {IsLocalRing.closedPoint R}) :
    PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩
      Module.support R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hxC) ⊆ {IsLocalRing.closedPoint R} := by
  obtain ⟨hP, hr⟩ := step_kernel_contains V D B s hs x hxD hxB C hxC hC
  intro q hq
  have hCq : (StalkPrimeQuotient.Constructions.kernelPrime V.carrier C.val x hxC).asIdeal ≤ q.asIdeal := by
    have h := Module.mem_support_iff_of_finite.mp hq.2
    rwa [Ideal.annihilator_quotient] at h
  apply hi
  constructor
  · change Ideal.ofList (r :: rs) ≤ q.asIdeal
    rw [Ideal.ofList_cons]
    exact sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hCq hr))) hq.1
  · apply Module.mem_support_iff_of_finite.mpr
    rw [Ideal.annihilator_quotient]
    exact hP.trans hCq

end AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions

end

end OAI
