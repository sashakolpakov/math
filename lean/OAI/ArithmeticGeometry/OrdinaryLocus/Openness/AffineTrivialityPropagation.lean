import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.RelativeFrameGluing
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenFrame
import Mathlib.Topology.Irreducible

/-! # Affine Triviality Propagation -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineTrivialityPropagation.Construction

noncomputable section

/-! Propagate a trivial fiber through intersecting affine opens of an irreducible base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem predicate_everywhere_of_affine_propagation
    {S : Scheme.{u}} [PreirreducibleSpace S] (P : S → Prop)
    (hlocal : ∀ (U : S.Opens), IsAffineOpen U → ∀ x ∈ U, ∀ y ∈ U, P x → P y)
    (x₀ : S) (hx₀ : P x₀) : ∀ x : S, P x := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (show x₀ ∈ (⊤ : S.Opens) from trivial)
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨z, hzU, hzV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen ⟨x₀, hxU⟩ ⟨x, hxV⟩
  exact hlocal V hV z hzV x hxV (hlocal U hU x₀ hxU z hzU hx₀)

theorem lineBundle_trivial_of_affine_fiber_propagation
    {X S : Scheme.{u}} [PreirreducibleSpace S]
    (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    (hf : ∀ U : S.Opens, IsIso (π.app U)) (L : X.Modules) (hL : LineBundle.Construction.IsLineBundle L)
    (e : (Scheme.Modules.pullback s).obj L ≅ LineBundle.Construction.structureSheafModule S)
    (hlocal : ∀ (U : S.Opens), IsAffineOpen U →
      (∃ x ∈ U, Nonempty ((Scheme.Modules.pullback (π.fiberι x)).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber x))) →
      Nonempty ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj L ≅ LineBundle.Construction.structureSheafModule (π ⁻¹ᵁ U).toScheme))
    (x₀ : S)
    (he : Nonempty ((Scheme.Modules.pullback (π.fiberι x₀)).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber x₀))) :
    Nonempty (L ≅ LineBundle.Construction.structureSheafModule X) := by
  let P := fun x : S ↦ Nonempty ((Scheme.Modules.pullback (π.fiberι x)).obj L ≅ LineBundle.Construction.structureSheafModule (π.fiber x))
  have hall : ∀ x : S, P x := by
    apply predicate_everywhere_of_affine_propagation P _ x₀ he
    intro U hU x hx y hy hPx
    obtain ⟨eU⟩ := hlocal U hU ⟨x, hx, hPx⟩
    exact ⟨AlgebraicGeometry.Quotients.FiniteDescent.OpenFrame.Construction.OpenFrameFibers.fiberIso π ⟨L, hL⟩ U y hy eU⟩
  apply RelativeFrameGluing.Construction.lineBundle_trivial_of_relative_frames π s hs hf L _ e
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  exact ⟨U, hxU, hlocal U hU ⟨x, hxU, hall x⟩⟩

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineTrivialityPropagation.Construction
