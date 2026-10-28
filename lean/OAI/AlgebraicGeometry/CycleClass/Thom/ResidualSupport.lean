import OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientCodimension
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientSectionOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep

/-! # Residual Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions

noncomputable section

/-! Each actual residual minimal prime is an original cycle support in
the next grading, and its source order is the faithful section-step
coefficient of that support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientCodimension.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.SupportQuotientSectionOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SupportSectionGerm.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.PrincipalSchemeOrder.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (x : V.carrier) (hxD : x ∈ (D.val : Set V.carrier))
  (r : V.carrier.presheaf.stalk x) (hn : IsSMulRegular (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) r)

local notation "R" => V.carrier.presheaf.stalk x
local notation "P" => PrimeSpectrum.asIdeal (OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD)

local instance : Ideal.IsPrime P := (StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD).isPrime

def residualCycleSupport (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) : Geometric.DimensionCycles.DimensionCycleSupport V (p + 1) :=
  SupportQuotientCodimension.Constructions.quotientCycleSupport V D x hxD (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)
    ((idealHeight_eq_coheight (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD)) (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)).symm.trans
      (TorAlgebra.SchemeOrderStep.source_prime_height_one R P r t hn))

variable (B : V.carrier.Opens) [Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B)]
  (s : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hs : Affine.SectionFunction.Constructions.parentSectionFunction D B s ≠ 0) (hxB : x ∈ B)

theorem residualCycleSupport_coefficient
    (hr : r = V.carrier.presheaf.germ B x hxB (B.topIso.hom s)) (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) :
    ((Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD))).ord
      (Affine.PrincipalSchemeOrder.Constructions.affineFunction (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD)
        (algebraMap R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) r)) (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t) : ℚ) =
    Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs (residualCycleSupport V D x hxD r hn t) := by
  let : Nonempty (D.inclusion ⁻¹ᵁ B) :=
    ⟨⟨IntersectionGeometry.supportPreimage D.val x hxD, SupportSectionGerm.Constructions.supportPreimage_mem_open V.carrier D.val x hxD B hxB⟩⟩
  rw [Section.CupPrincipalGeneral.Constructions.Step.principalStep_coefficient]
  have he := SupportQuotientSectionOrder.Constructions.principalCoefficient_quotientSupport V.presentation D.val x hxD B hxB (B.topIso.hom s)
    (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t)
  exact (congrArg (fun a : R => ((Spec (.of (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD))).ord
      (Affine.PrincipalSchemeOrder.Constructions.affineFunction (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD)
        (algebraMap R (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier D.val x hxD) a)) (TorAlgebra.SourceOrderStep.residualSourcePrime R P r t) : ℚ)) hr).trans he

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions
