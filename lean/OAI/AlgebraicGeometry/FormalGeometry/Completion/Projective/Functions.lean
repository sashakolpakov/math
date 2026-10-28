import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LiteralCycles
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ComparisonCech
import OAI.AlgebraicGeometry.FormalGeometry.Completion.IdempotentObstruction

/-! # Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Functions.Construction

noncomputable section

/-! Actual projective formal functions and connectedness from the infinitesimal idempotent obstruction. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (CommRingCat.of R))

/-- The existing actual formal-functions comparison is surjective for a flat projective
family whose actual global functions equal the base. -/
theorem projective_formalFunctionsComparison_surjective [Flat f] [IsIso f.appTop]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) (I : Ideal R) :
    Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison I f) :=
  ComparisonCech.Construction.formalFunctionsComparison_surjective_of_cech I f
    (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.cover (Over.mk f) P)
    (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.affine (Over.mk f) P)
    (Quotients.FiniteDescent.ProjectiveCechAt.Construction.ProjectiveCechComplex.covers (Over.mk f) P)
    (LiteralCycles.Construction.projectiveLiteralCech_formalZeroCycleComparisonSurjective f P I)

omit [X.IsSeparated] in
/-- Surjectivity of the actual formal-functions map contradicts every nontrivial clopen
piece of the actual initial infinitesimal fiber. -/
theorem infinitesimal_preconnected_of_formalFunctionsComparison_surjective [IsLocalRing R]
    (h : Function.Surjective (FunctionsComparison.Construction.formalFunctionsComparison (IsLocalRing.maximalIdeal R) f)) :
    PreconnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0) := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  by_cases hzero : s = ∅
  · exact Or.inl hzero
  by_cases hone : s = Set.univ
  · exact Or.inr hone
  exfalso
  let U : (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0).Opens := ⟨s, hs.isOpen⟩
  have hUzero : U ≠ ⊥ := fun hu => hzero (congrArg TopologicalSpace.Opens.carrier hu)
  have hUone : U ≠ ⊤ := fun hu => hone (congrArg TopologicalSpace.Opens.carrier hu)
  exact IdempotentObstruction.Construction.infinitesimalClopenIndicator_not_mem_comparison_range f U hs.isClosed hUzero hUone
    (h (Infinitesimal.ClopenSections.Construction.infinitesimalClopenIndicator (IsLocalRing.maximalIdeal R) f U hs.isClosed))

/-- The actual special fiber of the flat projective family cannot split into clopen pieces. -/
theorem projective_infinitesimal_preconnected [IsLocalRing R] [Flat f] [IsIso f.appTop]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) :
    PreconnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0) :=
  infinitesimal_preconnected_of_formalFunctionsComparison_surjective f
    (projective_formalFunctionsComparison_surjective f P (IsLocalRing.maximalIdeal R))

omit [X.IsSeparated] [IsNoetherianRing R] in
theorem infinitesimal_initial_nonempty_of_surjective [IsLocalRing R] [Surjective f] :
    Nonempty (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0) := by
  have : Nontrivial (R ⧸ (IsLocalRing.maximalIdeal R) ^ (0 + 1)) := by
    simpa only [Nat.zero_add, pow_one] using
      (inferInstance : Nontrivial (R ⧸ IsLocalRing.maximalIdeal R))
  have hn : Nonempty (Infinitesimal.Neighborhoods.Construction.infinitesimalBase (IsLocalRing.maximalIdeal R) 0) :=
    inferInstanceAs (Nonempty (Spec _))
  exact ⟨((pullback.snd f (Infinitesimal.Neighborhoods.Construction.infinitesimalBaseToSpec (IsLocalRing.maximalIdeal R) 0)).surjective
    hn.some).choose⟩

/-- The actual initial infinitesimal fiber is connected for the surjective flat projective family. -/
theorem projective_infinitesimal_connected [IsLocalRing R] [Flat f] [Surjective f] [IsIso f.appTop]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk f)) :
    ConnectedSpace (Infinitesimal.Neighborhoods.Construction.infinitesimalNeighborhood (IsLocalRing.maximalIdeal R) f 0) := by
  have := projective_infinitesimal_preconnected f P
  have := infinitesimal_initial_nonempty_of_surjective f
  exact ⟨inferInstance⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.Functions.Construction
