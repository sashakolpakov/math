import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertNumerics
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.PushforwardExact
import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertAdditivity
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

/-! # Closed Hilbert Additivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity

noncomputable section

/-! Hilbert polynomials on an actual closed projective scheme are additive
on actual coherent short exact sequences. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ} {X : Scheme.{u}}
  (f : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)) [IsClosedImmersion f]

theorem closedProjectiveHilbertPolynomial_add_of_shortExact
    (T : ShortComplex X.Modules) (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent] [T.X₃.IsQuasicoherent]
    [T.X₁.IsFiniteType] [T.X₂.IsFiniteType] [T.X₃.IsFiniteType]
    (j : Fin (r + 1)) :
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f T.X₂ j =
      ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f T.X₁ j + ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f T.X₃ j := by
  let S := T.map (Scheme.Modules.pushforward f)
  have : S.X₁.IsQuasicoherent := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₁
  have : S.X₂.IsQuasicoherent := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₂
  have : S.X₃.IsQuasicoherent := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_quasicoherent f T.X₃
  have : S.X₁.IsFiniteType := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₁
  have : S.X₂.IsFiniteType := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₂
  have : S.X₃.IsFiniteType := ClosedHilbertNumerics.Construction.coherentClosedDirectImage_finiteType f T.X₃
  exact HilbertAdditivity.Construction.projectiveHilbertPolynomial_add_of_shortExact S (Affine.PushforwardExact.Construction.affineModulePushforward_shortExact f hT) j

def closedProjectiveCokernelHilbertPolynomial
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (a : M ⟶ N) (j : Fin (r + 1)) : Polynomial ℚ := by
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel a
  have := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel a
  exact ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f (cokernel a) j

theorem closedProjectiveCokernelHilbertPolynomial_eq_sub
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType] [N.IsFiniteType]
    (a : M ⟶ N) [Mono a] (j : Fin (r + 1)) :
    closedProjectiveCokernelHilbertPolynomial f a j =
      ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f N j - ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j := by
  have := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel a
  have := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel a
  let T := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hT : T.ShortExact := { exact := ShortComplex.cokernelSequence_exact a }
  have he := closedProjectiveHilbertPolynomial_add_of_shortExact f T hT j
  change ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f N j =
    ClosedHilbertNumerics.Construction.closedProjectiveHilbertPolynomial f M j + closedProjectiveCokernelHilbertPolynomial f a j at he
  rw [he, add_sub_cancel_left]

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedHilbertAdditivity
