import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # Support -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Connected reduced total spaces and reduced self-products of abelian schemes over a field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {K : Type u} [Field K] {g : ℕ}

theorem Abelian.Schemes.AbelianScheme.geometricallyReduced (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    GeometricallyReduced A.scheme.hom := Smooth.ReducedFibers.smooth_geometricallyReduced A.scheme.hom

theorem Abelian.Schemes.AbelianScheme.reduced_overField (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) : IsReduced A.scheme.left :=
  Smooth.ReducedFibers.smoothOverField_isReduced A.scheme.hom

theorem Abelian.Schemes.AbelianScheme.connected_overField (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) : ConnectedSpace A.scheme.left :=
  GeometricallyConnected.connectedSpace_of_subsingleton A.scheme.hom

theorem Abelian.Schemes.AbelianScheme.selfProduct_reduced_overField (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) :
    IsReduced (A.scheme ⊗ A.scheme).left := by
  change IsReduced (Limits.pullback A.scheme.hom A.scheme.hom)
  exact Smooth.ReducedFibers.smoothOverField_isReduced (Limits.pullback.snd A.scheme.hom A.scheme.hom ≫ A.scheme.hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
