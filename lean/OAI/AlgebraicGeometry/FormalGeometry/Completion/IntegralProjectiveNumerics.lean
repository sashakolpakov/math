import OAI.AlgebraicGeometry.FormalGeometry.Completion.CoherentHilbertLeading
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.DomainFunctions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

/-! # Integral Projective Numerics -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics

noncomputable section

/-! The coherent Hilbert comparison on an integral closed projective scheme
over an infinite field, with all global-function and finiteness hypotheses derived. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

include f

def closedProjectiveStructure : X ⟶ Spec (CommRingCat.of K) :=
  f ≫ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace K r).hom

instance closedProjectiveStructure_proper : IsProper (closedProjectiveStructure f) := by
  unfold closedProjectiveStructure
  infer_instance

theorem closedProjective_locallyNoetherian : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (closedProjectiveStructure f)

theorem closedProjective_compact : CompactSpace X :=
  QuasiCompact.compactSpace_of_compactSpace (closedProjectiveStructure f)

variable [IsIntegral X]

theorem integralClosedProjective_globalFunctions_isField : IsField Γ(X, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some (inferInstance : Nonempty X), trivial⟩⟩
  exact Proper.DomainFunctions.Construction.proper_globalFunctionDomain_isField K (closedProjectiveStructure f)

omit [IsClosedImmersion f] in
theorem integralClosedProjective_globalFunctions_infinite [Infinite K] : Infinite Γ(X, ⊤) := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some (inferInstance : Nonempty X), trivial⟩⟩
  let a := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (closedProjectiveStructure f).appTop
  exact Infinite.of_injective a.hom a.hom.injective

theorem integralClosedProjective_coherentLineBundle_hilbert_degree_leadingCoeff [Infinite K]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (j : Fin (r + 1)) :
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).natDegree =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).natDegree ∧
    (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (CoherentLineBundleTensor.Construction.coherentLineBundleTensor M L) j).leadingCoeff =
      (ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j).leadingCoeff := by
  have : IsLocallyNoetherian X := closedProjective_locallyNoetherian f
  have : CompactSpace X := closedProjective_compact f
  have : Infinite Γ(X, ⊤) := integralClosedProjective_globalFunctions_infinite f
  exact CoherentHilbertLeading.Construction.coherentLineBundle_hilbert_degree_leadingCoeff
    (integralClosedProjective_globalFunctions_isField f) f M L j

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralProjectiveNumerics
