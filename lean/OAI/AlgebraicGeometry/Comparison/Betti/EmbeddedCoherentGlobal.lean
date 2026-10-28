import OAI.AlgebraicGeometry.Comparison.Betti.Closed.AnalytificationPushforwardAdditiveSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Coherent

/-! # Embedded Coherent Global -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentGlobal

noncomputable section

/-! The original global-section comparison is an isomorphism for coherent modules on every smooth integral closed subvariety of positive-dimensional projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Projective.Coherent.Dolbeault

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem embeddedCoherentGlobalSectionsMap_isIso
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) [IsClosedImmersion f.left]
    (M : X.left.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    IsIso (Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationGlobalSectionsMap X M) := by
  let N := (Scheme.Modules.pushforward f.left).obj M
  let : N.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f.left
  let : N.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f.left
  apply Closed.AnalytificationPushforwardAdditiveSquare.moduleAnalytificationGlobalSectionsMap_isIso_closed f M
  exact Projective.Coherent.Dolbeault.projectiveCoherentGlobalSectionsMap_isIso n N

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentGlobal
