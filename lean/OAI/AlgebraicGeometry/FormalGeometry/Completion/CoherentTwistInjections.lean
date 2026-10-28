import OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularTensorSection
import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentLineBundleTensor
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.SectionGeneration

/-! # Coherent Twist Injections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentTwistInjections

noncomputable section

/-! Injections comparing an arbitrary coherent module and its tensor product
with a line bundle after sufficiently positive projective twists. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  [IsLocallyNoetherian X] [CompactSpace X] [Infinite Γ(X, ⊤)]
  (hfield : IsField Γ(X, ⊤))
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

include hfield

theorem closedProjectiveModuleLineBundle_eventually_injection
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ a : M ⟶ ClosedHilbertNumerics.Construction.closedProjectiveTwist f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j n, Mono a := by
  obtain ⟨b, hb⟩ := Projective.SectionGeneration.Construction.closedProjectiveLineBundleTwist_eventually_hasFrameSections f L j
  refine ⟨b, fun n hn => ?_⟩
  let hg := hb n hn
  obtain ⟨a, ha⟩ := RegularTensorSection.Construction.exists_mono_tensor_generated_lineBundle hfield hg.lineBundle hg M
  have := ha
  let T := (Scheme.Modules.pullback f).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n)
  exact ⟨a ≫ (α_ M L.sheaf T).inv, inferInstance⟩

theorem closedProjectiveModuleLineBundle_eventually_injections
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (a : M ⟶ ClosedHilbertNumerics.Construction.closedProjectiveTwist f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j n)
        (c : CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L ⟶ ClosedHilbertNumerics.Construction.closedProjectiveTwist f M j n), Mono a ∧ Mono c := by
  obtain ⟨b, hb⟩ := closedProjectiveModuleLineBundle_eventually_injection hfield f M L j
  obtain ⟨d, hd⟩ := closedProjectiveModuleLineBundle_eventually_injection hfield f
    (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) (Quotients.FiniteDescent.DualLine.Construction.DualLineBundle.dual L) j
  refine ⟨max b d, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hb n ((le_max_left _ _).trans hn)
  obtain ⟨c, hc⟩ := hd n ((le_max_right _ _).trans hn)
  have := hc
  let T := (Scheme.Modules.pullback f).obj
    (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := K) j n)
  let e := CoherentLineBundleTensor.Construction.coherentLineBundleTensor_cancelDualIso M L ⊗ᵢ Iso.refl T
  exact ⟨a, c ≫ e.hom, ha, inferInstance⟩

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentTwistInjections
