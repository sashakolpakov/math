import OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep
import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientPoints
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.OrderMinimalPrime
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SupportCodimension

/-! # Residual Equiv -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualEquiv.Constructions

noncomputable section

/-! The actual residual minimal primes are exactly the nonzero
original section-step supports through the chosen scheme point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSourceEquiv.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientPoints.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientCodimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientSectionOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.OrderMinimalPrime.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SupportCodimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.ClosedSupport.Constructions.Principal
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

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
local notation "hn" => OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference.sectionQuotientRegular V D B s hs x hxD hxB
local notation "F" => OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions.residualCycleSupport V D x hxD r hn

local instance : Ideal.IsPrime P := (StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD).isPrime

theorem residualCycleSupport_injective : Function.Injective F := by
  intro t u h
  apply ResidualSourceEquiv.Constructions.residualSourcePrime_injective R P r
  apply SupportQuotientPoints.Constructions.quotientSupport_injective V.carrier D.val x hxD
  exact congrArg Subtype.val h

theorem residualCycleSupport_nonzero (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs (F t) ≠ 0 := by
  rw [← ResidualSupport.Constructions.residualCycleSupport_coefficient V D x hxD r hn B s hs hxB rfl t]
  have h := (Affine.OrderMinimalPrime.Constructions.schemeOrder_ne_zero_iff_minimal Q (algebraMap R Q r)
    (TorAlgebra.SchemeOrderStep.equation_image_ne_zero R P r hn) (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)
    (TorAlgebra.SchemeOrderStep.source_prime_height_one R P r t hn)).mpr (ResidualSourceEquiv.Constructions.residualSourcePrime_minimal R P r t)
  exact_mod_cast h

theorem residualCycleSupport_contains (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    x ∈ ((F t).val : Set V.carrier) :=
  SupportQuotientPoints.Constructions.point_mem_quotientSupport V.carrier D.val x hxD (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)

theorem exists_residualCycleSupport (C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1))
    (hxC : x ∈ (C.val : Set V.carrier)) (hC : Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C ≠ 0) :
    ∃ t : TorAlgebra.SourceOrderStep.ResidualComponent R P r, F t = C := by
  have hcoef := hC
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient] at hcoef
  have hCD := (Section.ClosedSupport.Constructions.Principal.principalCoefficient_support D B s C.val hcoef).1
  obtain ⟨q, hqC⟩ := SupportQuotientPoints.Constructions.exists_quotientSupport V.carrier D.val x hxD C.val hCD hxC
  have hd : V.presentation.supportCodimension (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport V.carrier D.val x hxD q) =
      V.presentation.supportCodimension D.val + 1 := by
    rw [hqC, Integral.ProductSupport.Constructions.integralPresentation_supportCodimension, Integral.ProductSupport.Constructions.integralPresentation_supportCodimension,
      C.property, D.property]
  have hc := Relative.SupportCodimension.Constructions.supportPreimage_coheight_one V.presentation D.val
    (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport V.carrier D.val x hxD q) (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport_mem_parent V.carrier D.val x hxD q) hd
  rw [← StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport_preimage] at hc
  have hqh : Order.coheight q = 1 :=
    (SupportQuotientCodimension.Constructions.quotientSupportMap_coheight V.carrier D.val x hxD q).symm.trans hc
  have hheight : q.asIdeal.height = 1 := (idealHeight_eq_coheight (.of Q) q).trans hqh
  let : Nonempty (D.inclusion ⁻¹ᵁ B) :=
    ⟨⟨IntersectionGeometry.supportPreimage D.val x hxD, SupportSectionGerm.Constructions.supportPreimage_mem_open V.carrier D.val x hxD B hxB⟩⟩
  have he := SupportQuotientSectionOrder.Constructions.principalCoefficient_quotientSupport V.presentation D.val x hxD B hxB (B.topIso.hom s) q
  rw [hqC] at he
  have ho : (Spec (.of Q)).ord (Affine.PrincipalSchemeOrder.Constructions.affineFunction Q (algebraMap R Q r)) q ≠ 0 := by
    intro hz
    apply hcoef
    exact he.symm.trans (by rw [hz, Int.cast_zero])
  have hmin := (Affine.OrderMinimalPrime.Constructions.schemeOrder_ne_zero_iff_minimal Q (algebraMap R Q r)
    (TorAlgebra.SchemeOrderStep.equation_image_ne_zero R P r hn) q hheight).mp ho
  obtain ⟨t, ht⟩ := ResidualSourceEquiv.Constructions.exists_residualSourcePrime R P r q hmin
  refine ⟨t, Subtype.ext ?_⟩
  exact (congrArg (StalkPrimeQuotient.Constructions.SupportScheme.quotientSupport V.carrier D.val x hxD) ht).trans hqC

def residualCycleEquiv : TorAlgebra.SourceOrderStep.ResidualComponent R P r ≃
    {C : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1) // x ∈ (C.val : Set V.carrier) ∧ Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs C ≠ 0} :=
  Equiv.ofBijective (fun t => ⟨F t, residualCycleSupport_contains V D B s hs x hxD hxB t,
    residualCycleSupport_nonzero V D B s hs x hxD hxB t⟩) (by
    constructor
    · intro t u h
      exact residualCycleSupport_injective V D B s hs x hxD hxB (congrArg Subtype.val h)
    · intro C
      obtain ⟨t, ht⟩ := exists_residualCycleSupport V D B s hs x hxD hxB C.val C.property.1 C.property.2
      exact ⟨t, Subtype.ext ht⟩)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualEquiv.Constructions
