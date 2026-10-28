import OAI.AlgebraicGeometry.FormalGeometry.Completion.FunctionsComparison
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Comparison Injective -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonInjective.Construction

noncomputable section

/-! # Completion: injectivity of the actual completion comparison for faithfully flat families -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- A flat surjective family induces an injection on actual global functions. -/
theorem flat_surjective_appTop_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] :
    Function.Injective f.appTop := by
  have : Epi f := Flat.epi_of_flat_of_surjective f
  have : Mono f.appTop := by
    rw [← Scheme.Γ_map_op]
    infer_instance
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback f.appTop).mp inferInstance

/-- Every infinitesimal structure-ring map is injective for the actual flat surjective family. -/
theorem infinitesimalBaseSectionsMap_injective {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [Surjective f] (n : ℕ) :
    Function.Injective (FunctionsComparison.Construction.infinitesimalBaseSectionsMap I f n) := by
  exact (flat_surjective_appTop_injective (pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec I n))).comp
    (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).symm.commRingCatIsoToRingEquiv.injective

/-- The actual completed-base comparison is injective for every flat surjective family. -/
theorem formalFunctionsComparison_injective {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [Surjective f] :
    Function.Injective (FunctionsComparison.Construction.formalFunctionsComparison I f) := by
  intro x y h
  apply AdicCompletion.ext_evalₐ
  intro n
  cases n with
  | zero =>
      have : Subsingleton (R ⧸ I ^ 0) := by
        rw [show I ^ 0 = ⊤ by simp]
        infer_instance
      exact Subsingleton.elim _ _
  | succ n =>
      apply infinitesimalBaseSectionsMap_injective I f n
      exact congrArg (fun s : Infinitesimal.ClopenSections.Construction.infinitesimalGlobalSections I f => s.val n) h

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonInjective.Construction
