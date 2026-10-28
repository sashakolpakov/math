import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler
import OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation
import OAI.AlgebraicGeometry.CycleClass.Thom.ResidualTailAmbientEuler

/-! # Principal Step Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepEuler.Constructions

noncomputable section

/-! Exact one-step recursion for the native local Tor Euler
characteristic, using the actual original principal-step cycle and
the original ambient ring for the remaining equations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace RingTheory.Sequence
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep.Constructions.Reference OAI.AlgebraicGeometry.CycleClass.Thom.ResidualSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ResidualEquiv.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepIsolation.Constructions.ResidualStalkPrime OAI.AlgebraicGeometry.CycleClass.Thom.ResidualTailAmbientEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.CupPrincipalGeneral.Constructions.Step OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.SourceOrderStep OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.EulerTransport.Tor

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

theorem principalStep_euler_sum (rs : List R) (d : ℕ) :
    Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs) =
      ∑ t : TorAlgebra.SourceOrderStep.ResidualComponent R P r, Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs (F t) *
        Local.Euler.Constructions.supportEuler V (p + 1) x rs d (F t) := by
  rw [Local.Euler.Constructions.localCycleEuler_eq_filter_sum]
  symm
  apply Finset.sum_bij (fun t _ => F t)
  · intro t _
    exact Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (ResidualEquiv.Constructions.residualCycleSupport_nonzero V D B s hs x hxD hxB t),
        ResidualEquiv.Constructions.residualCycleSupport_contains V D B s hs x hxD hxB t⟩
  · intro t _ u _ h
    exact ResidualEquiv.Constructions.residualCycleSupport_injective V D B s hs x hxD hxB h
  · intro C hC
    obtain ⟨hc, hx⟩ := Finset.mem_filter.mp hC
    obtain ⟨t, ht⟩ := ResidualEquiv.Constructions.exists_residualCycleSupport V D B s hs x hxD hxB C hx (Finsupp.mem_support_iff.mp hc)
    exact ⟨t, Finset.mem_univ _, ht⟩
  · intro t _
    rfl

theorem residualTailEuler_eq_supportEuler (rs : List R)
    (hr : IsWeaklyRegular R (r :: rs))
    (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal R)
    (t : TorAlgebra.SourceOrderStep.ResidualComponent R P r) (d : ℕ) :
    ReferenceSectionEulerStep.Constructions.Reference.residualTailEuler V D B s x hxD hxB rs t d = Local.Euler.Constructions.supportEuler V (p + 1) x rs d (F t) :=
  (ResidualTailAmbientEuler.Constructions.residual_tail_euler_eq_ambient R r rs hr hm
    (ModuleCat.of (R ⧸ Ideal.span {r}) ((R ⧸ Ideal.span {r}) ⧸ t.val.asIdeal)) d).trans
    ((TorAlgebra.EulerTransport.Tor.iso_right R (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (PrincipalStepIsolation.Constructions.ResidualStalkPrime.residualQuotientIso V D x hxD r hn t) d).trans
      (Local.Euler.Constructions.supportEuler_of_mem V (p + 1) x rs d (F t)
        (ResidualEquiv.Constructions.residualCycleSupport_contains V D B s hs x hxD hxB t)).symm)

theorem euler_eq_principalStep (rs : List R)
    (hr : IsWeaklyRegular R (r :: rs))
    (hm : ∀ a ∈ r :: rs, a ∈ IsLocalRing.maximalIdeal R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R Q ⊆ {IsLocalRing.closedPoint R})
    (d : ℕ) (hd : rs.length ≤ d) :
    TorAlgebra.Euler.Tor.euler R (ModuleCat.of R (R ⧸ Ideal.ofList (r :: rs))) (ModuleCat.of R Q) d =
      Local.Euler.Constructions.localCycleEuler V (p + 1) x rs d (Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs) := by
  rw [principalStep_euler_sum V D B s hs x hxD hxB rs d]
  apply (ReferenceSectionEulerStep.Constructions.Reference.euler_eq_original_section_sum V D B s hs x hxD hxB rs hr hm hi d hd).trans
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (fun a => Section.CupPrincipalGeneral.Constructions.Step.principalStep D B s hs (F t) * a)
    (residualTailEuler_eq_supportEuler V D B s hs x hxD hxB rs hr hm t d)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalStepEuler.Constructions
