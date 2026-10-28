import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Point
import Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Point Topology -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointTopology.Construction

noncomputable section

/-!
# Completion: covering sieves at a geometric point

Every covering sieve on the identity object in the pro-étale site of an
algebraically closed field contains the identity.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- The identity object of the geometric point's pro-étale site. -/
abbrev geometricPointProEtTerminal : (Spec (CommRingCat.of K)).ProEt :=
  Scheme.ProEt.mk (𝟙 _)

/-- The identity object is terminal. -/
def geometricPointProEtIsTerminal : IsTerminal (geometricPointProEtTerminal K) :=
  IsTerminal.ofUniqueHom
    (fun U ↦ MorphismProperty.Over.homMk U.hom)
    (fun U f ↦ MorphismProperty.Over.Hom.ext (by simpa using f.w))

/-- Every covering sieve of the geometric point's identity object is maximal. -/
theorem geometricPoint_coveringSieve_eq_top
    (S : Sieve (geometricPointProEtTerminal K))
    (hS : S ∈ Scheme.ProEt.topology (Spec (CommRingCat.of K)) _) : S = ⊤ := by
  have : (Scheme.ProEt.precoverage (Spec (CommRingCat.of K))).IsStableUnderComposition := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  have : (Scheme.ProEt.precoverage (Spec (CommRingCat.of K))).IsStableUnderBaseChange := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  have : (Scheme.ProEt.precoverage (Spec (CommRingCat.of K))).HasIsos := by
    unfold Scheme.ProEt.precoverage
    infer_instance
  obtain ⟨R, hR, hRS⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hS
  have hR' : R.map (Scheme.ProEt.forget _ ⋙ Over.forget _) ∈
      Scheme.precoverage @WeaklyEtale (Spec (CommRingCat.of K)) := hR.2
  obtain ⟨Y, g, hg, y, _⟩ := Scheme.JointlySurjective.exists_eq
    _ hR' (IsLocalRing.closedPoint K)
  obtain @⟨U, a, hU⟩ := hg
  obtain ⟨s, hs⟩ := Point.Construction.weaklyEtale_exists_section U.hom y
  let t : geometricPointProEtTerminal K ⟶ U := MorphismProperty.Over.homMk s hs
  have ha : S a := hRS _ _ hU
  have ht : t ≫ a = 𝟙 _ := (geometricPointProEtIsTerminal K).hom_ext _ _
  exact Sieve.id_mem_iff_eq_top.mp (ht ▸ S.downward_closed ha t)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.PointTopology.Construction
