import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalSetup
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Functions

/-! # Comparison Property -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonProperty.Construction

noncomputable section

/-! Compact propositions for surjectivity of the existing actual formal-functions maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Literally surjectivity of the previously constructed ring homomorphism. The compact
proposition prevents elaboration from repeatedly expanding geometric stalk types. -/
def FormalFunctionsComparisonSurjective {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I f)

/-- The same actual surjectivity property for the literal normalized local family. -/
def NormalizedLocalFormalComparisonSurjective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (n : f.normalization) : Prop :=
  FormalFunctionsComparisonSurjective
    (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n)) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n)

theorem normalizedLocalFormalComparisonSurjective_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (n : f.normalization) :
    NormalizedLocalFormalComparisonSurjective f n ↔
      Function.Surjective (NormalizedLocalSetup.Construction.normalizedLocalFormalComparison f n) := Iff.rfl

/-- The proved idempotent obstruction applies directly to this actual surjectivity property. -/
theorem normalizedLocal_initial_connected_of_formal_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (n : f.normalization)
    [IsNoetherianRing (f.normalization.presheaf.stalk n)]
    (hs : Surjective (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n))
    (h : NormalizedLocalFormalComparisonSurjective f n) :
    ConnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood
      (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n)) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) 0) := by
  have : Surjective (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) := hs
  have : PreconnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood
      (IsLocalRing.maximalIdeal (f.normalization.presheaf.stalk n)) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) 0) :=
    Projective.Functions.Construction.infinitesimal_preconnected_of_formalFunctionsComparison_surjective
      (R := f.normalization.presheaf.stalk n) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n) h
  exact ⟨Projective.Functions.Construction.infinitesimal_initial_nonempty_of_surjective
    (R := f.normalization.presheaf.stalk n) (NormalizedLocalFunctions.Construction.normalizedLocalFamily f n)⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonProperty.Construction
