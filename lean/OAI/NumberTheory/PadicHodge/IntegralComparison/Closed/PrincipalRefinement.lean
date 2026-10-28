import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.EtaleCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.ClosedSections

/-! # Principal Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PrincipalRefinement

noncomputable section

/-! Principal neighborhoods on a closed subscheme are restrictions of
actual principal neighborhoods in the ambient scheme. Smoothness supplies
such neighborhoods with étale coordinates around each original point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U)

include hU

theorem lift (s : Γ(X, f ⁻¹ᵁ U)) :
    ∃ r : Γ(Y, U), f.app U r = s ∧ f ⁻¹ᵁ Y.basicOpen r = X.basicOpen s := by
  obtain ⟨r, hr⟩ := f.app_surjective U hU s
  exact ⟨r, hr, by rw [Scheme.preimage_basicOpen, hr]⟩

theorem exists_coordinate_refinement
    (k : Type u) [CommRing k] [Algebra k Γ(X, f ⁻¹ᵁ U)]
    [Algebra.Smooth k Γ(X, f ⁻¹ᵁ U)] (x : X) (hx : f x ∈ U) :
    ∃ r : Γ(Y, U), f x ∈ Y.basicOpen r ∧
      IntegralComparison.Smooth.EtaleCoordinates.HasCoordinates k Γ(X, f ⁻¹ᵁ U) (f.app U r) := by
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  let q := hV.primeIdealOf ⟨x, hx⟩
  obtain ⟨s, hs, hcoord⟩ := IntegralComparison.Smooth.EtaleCoordinates.exists_at_prime k Γ(X, V) q.asIdeal
  have hxs : x ∈ X.basicOpen s := by
    have hq : q ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hs
    change hV.fromSpec q ∈ X.basicOpen s at hq
    simpa only [q, hV.fromSpec_primeIdealOf] using hq
  obtain ⟨r, hr, hopen⟩ := lift f U hU s
  refine ⟨r, ?_, ?_⟩
  · change x ∈ f ⁻¹ᵁ Y.basicOpen r
    rw [hopen]
    exact hxs
  · rw [hr]
    exact hcoord

theorem exists_smooth_coordinate_refinement {S : Scheme.{u}} [IsAffine S]
    (π : Y ⟶ S) [Smooth (f ≫ π)] (x : X) (hx : f x ∈ U) :
    letI := IntegralComparison.Smooth.ClosedSections.algebra (f ≫ π) (f ⁻¹ᵁ U)
    ∃ r : Γ(Y, U), f x ∈ Y.basicOpen r ∧
      IntegralComparison.Smooth.EtaleCoordinates.HasCoordinates Γ(S, ⊤) Γ(X, f ⁻¹ᵁ U) (f.app U r) := by
  let := IntegralComparison.Smooth.ClosedSections.algebra (f ≫ π) (f ⁻¹ᵁ U)
  let := IntegralComparison.Smooth.ClosedSections.smooth_sections (f ≫ π) (f ⁻¹ᵁ U) (hU.preimage f)
  exact exists_coordinate_refinement f U hU Γ(S, ⊤) x hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PrincipalRefinement
