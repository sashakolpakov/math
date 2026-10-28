import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FactorizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphismOpenParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveParameterCuts

/-! # Parameter Quasi Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ParameterQuasiProjectivity

noncomputable section

/-! The actual factorization and isomorphism parameter loci have quasi-projective presentations over a noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def properFactorizationParameterQuasiProjectivePresentation
    {S : Scheme.{u}} [IsNoetherian S] (M : Over S) [IsLocallyNoetherian M.left]
    (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M) {X P Z : Over M.left}
    [IsProper X.hom] [Flat X.hom] (j : Z ⟶ P) [IsClosedImmersion j.left] (i : X ⟶ P) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (FactorizationParameter.properFactorizationParameter M j i) :=
  Q.ofClosedImmersion (FactorizationParameter.properFactorizationParameterInclusion M j i)

def isomorphismOpenParameterQuasiProjectivePresentation
    {S : Scheme.{u}} [IsNoetherian S] (M : Over S) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation M)
    {X Y : Over M.left} [IsProper Y.hom] (j : X ⟶ Y) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (IsomorphismOpenParameters.isomorphismOpenParameter M j) :=
  Q.openParameter (HilbertConstruction.Over.IsomorphismOpen.overIsomorphismOpen j)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.ParameterQuasiProjectivity
