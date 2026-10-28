import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing
import OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedEquationDimension

/-! # Reference Section Euler Step -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference

noncomputable section

/-! The actual isolated local Tor Euler characteristic reduces by a
regular section with exactly the original geometric principal-step
coefficients. Source regularity and the dimension bound are derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.StalkNonvanishing.Constructions.StepIntersectionCoefficient OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SchemeOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedEquationDimension.Constructions

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

local instance : Ideal.IsPrime P := (StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD).isPrime

include hs in
theorem sectionQuotientRegular : IsSMulRegular Q r := by
  have hn : r ∉ P := Section.StalkNonvanishing.Constructions.StepIntersectionCoefficient.section_supportStalk_ne_zero D B s hs x hxD hxB
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem P r).mpr
  intro a ha
  exact ((StalkPrimeQuotient.Constructions.kernelPrime V.carrier D.val x hxD).isPrime.mem_or_mem ha).resolve_left hn

def residualTailEuler (rs : List R) (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) (d : ℕ) : ℚ :=
  TorAlgebra.Euler.Tor.euler (R ⧸ Ideal.span {r})
    (ModuleCat.of (R ⧸ Ideal.span {r})
      ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))))
    (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ t.val.asIdeal)) d

theorem euler_eq_original_section_sum (rs : List R)
    (hr : IsWeaklyRegular R (r :: rs))
    (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R Q ⊆ {IsLocalRing.closedPoint R})
    (d : ℕ) (hd : rs.length ≤ d) :
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) (ModuleCat.of R Q) d =
      ∑ t : TorAlgebra.SourceOrderStep.ResidualComponent R P r,
        Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs
          (ResidualSupport.Constructions.residualCycleSupport V D x hxD r (sectionQuotientRegular V D B s hs x hxD hxB) t) *
        residualTailEuler V D B s x hxD hxB rs t d := by
  have hdim := IsolatedEquationDimension.Constructions.quotient_supportDim_le_length R P (r :: rs) hm hi
  have he := TorAlgebra.SchemeOrderStep.euler_eq_source_schemeOrder_sum R P r rs hr hm
    (sectionQuotientRegular V D B s hs x hxD hxB) hdim hi d hd
  apply he.trans
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun k => k * residualTailEuler V D B s x hxD hxB rs t d)
    (ResidualSupport.Constructions.residualCycleSupport_coefficient V D x hxD r (sectionQuotientRegular V D B s hs x hxD hxB) B s hs hxB rfl t)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference
