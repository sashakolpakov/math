import Mathlib

/-!
# Typed certification logic for polygon-counting arguments

This module isolates a reusable logical step that should not be left as an
inequality between unrelated natural numbers.  A classification of a geometric
locus which is constant along paths factors through its actual path-component
quotient.  If every advertised class is represented, the number of classes is
therefore at most the number of path components.

No topology theorem asserting path invariance is assumed here.  Instead it is
an explicit, typed field of `PathClassificationCertificate`, so downstream
applications must provide it for the actual configuration space and actual
classification map.
-/

namespace StickKnots

open Function

noncomputable section

universe u v

variable {X : Type u} {Class : Type v} [TopologicalSpace X]

/-- A classifier on a topological space, together with the two semantic facts
needed in a chamber-counting proof: it is invariant along genuine continuous
paths, and every target class under discussion is represented. -/
structure PathClassificationCertificate (X : Type u) (Class : Type v)
    [TopologicalSpace X] where
  classify : X → Class
  path_invariant : ∀ ⦃x y : X⦄ (_p : Path x y), classify x = classify y
  support : Surjective classify

namespace PathClassificationCertificate

variable (cert : PathClassificationCertificate X Class)

/-- The classifier induced on the actual quotient by path-connectedness. -/
def onPathComponents : ZerothHomotopy X → Class :=
  ZerothHomotopy.lift cert.classify cert.path_invariant

@[simp]
theorem onPathComponents_mk (x : X) :
    cert.onPathComponents (.mk x) = cert.classify x := rfl

/-- Support of the original classifier makes the induced map from path
components surjective. -/
theorem onPathComponents_surjective : Surjective cert.onPathComponents := by
  intro c
  obtain ⟨x, rfl⟩ := cert.support c
  exact ⟨ZerothHomotopy.mk x, rfl⟩

/-- A finite path-component space bounds the number of represented classes.
This is the typed cardinality bridge used by the knot-counting certificate. -/
theorem natCard_class_le_pathComponents
    (cert : PathClassificationCertificate X Class)
    [Finite (ZerothHomotopy X)] :
    Nat.card Class ≤ Nat.card (ZerothHomotopy X) :=
  Nat.card_le_card_of_surjective (onPathComponents cert)
    (onPathComponents_surjective cert)

end PathClassificationCertificate

/-- A homeomorphism induces an equivalence of the actual connected-component
quotients.  This small functorial bridge lets an external real-algebraic bound
be stated in polynomial coordinates and then transported to the geometric
configuration space without replacing either side by a free number. -/
noncomputable def connectedComponentsEquivOfHomeomorph
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y := by
  let f : ConnectedComponents X → ConnectedComponents Y :=
    e.continuous.connectedComponentsMap
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
    have h := congrArg e.symm.continuous.connectedComponentsMap hab
    simpa [f] using h
  · exact e.continuous.connectedComponentsMap_surjective e.surjective

@[simp]
theorem connectedComponentsEquivOfHomeomorph_mk
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) (x : X) :
    connectedComponentsEquivOfHomeomorph e (.mk x) = .mk (e x) := rfl

/-- A numerical component bound attached to the actual path-component type of
`X`, rather than to a free natural-number variable.  The proof of `bound` may
come from a separately supplied real-algebraic theorem. -/
structure PathComponentBound (X : Type u) [TopologicalSpace X] (B : ℕ) where
  finiteComponents : Finite (ZerothHomotopy X)
  bound : Nat.card (ZerothHomotopy X) ≤ B

/-- Complete composition of the semantic classification certificate and the
component-count certificate. -/
theorem class_count_le_of_certificates
    (cert : PathClassificationCertificate X Class)
    {B : ℕ} (components : PathComponentBound X B) :
    Nat.card Class ≤ B := by
  letI := components.finiteComponents
  exact (PathClassificationCertificate.natCard_class_le_pathComponents cert).trans
    components.bound

/-- On a locally path-connected space, mathlib identifies connected components
with path components.  This is the bridge needed to consume a component bound
stated using `ConnectedComponents`, as real-algebraic bounds normally are. -/
theorem natCard_pathComponents_eq_connectedComponents
    [LocallyPathConnectedSpace X] :
    Nat.card (ZerothHomotopy X) = Nat.card (ConnectedComponents X) :=
  Nat.card_congr connectedComponentsEquivZerothHomotopy.symm

end

end StickKnots
