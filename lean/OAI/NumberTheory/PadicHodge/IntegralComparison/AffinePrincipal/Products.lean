import OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Diagram
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.OpenProductPreservation
import OAI.NumberTheory.PadicHodge.IntegralComparison.FlasqueCechSubfamily

/-! # Products -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Products

noncomputable section

/-! The actual principal-open diagram preserves every nonempty finite
intersection, including after pullback to a special fibre. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v
variable (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)

def functor : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) ⥤ X.Opens :=
  Diagram.functor X U hU ⋙ GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X

def standard : AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U) ⥤ X.Opens :=
  AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor Γ(X, U) ⋙ hU.fromSpec.opensFunctor

def iso : standard X U hU ≅ Products.functor X U hU :=
  NatIso.ofComponents (fun r => eqToIso (hU.fromSpec_image_basicOpen r.val))
    (fun {_ _} _ => Subsingleton.elim _ _)

theorem preserves {ι : Type v} [Finite ι] [Nonempty ι]
    (r : ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)) [HasProduct r] :
    PreservesLimit (Discrete.functor r) (Products.functor X U hU) := by
  let himage : PreservesLimit (Discrete.functor ((AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor Γ(X, U)).obj ∘ r))
      hU.fromSpec.opensFunctor :=
    FlasqueCechSubfamily.openEmbedding_preserves hU.fromSpec.base
      hU.fromSpec.isOpenEmbedding _
  let : PreservesLimit
      (Discrete.functor ((Discrete.functor r ⋙ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor Γ(X, U)).obj ∘ Discrete.mk))
      hU.fromSpec.opensFunctor := by exact himage
  let : PreservesLimit (Discrete.functor r ⋙ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor Γ(X, U))
      hU.fromSpec.opensFunctor := preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := Discrete.functor r ⋙ AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.opensFunctor Γ(X, U))).symm
  let : PreservesLimit (Discrete.functor r) (standard X U hU) := by
    dsimp only [standard]
    infer_instance
  exact preservesLimit_of_natIso (Discrete.functor r) (iso X U hU)

theorem pullback_preserves (Y : Scheme.{u}) (f : Y ⟶ X)
    {ι : Type v} [Finite ι] [Nonempty ι]
    (r : ι → AlgebraicGeometry.Crystalline.Cohomology.PrincipalCoefficient.PrincipalCoefficientCategory.Object Γ(X, U)) [HasProduct r] :
    PreservesLimit (Discrete.functor r) (Products.functor X U hU ⋙ Opens.map f.base) := by
  let := preserves X U hU r
  let : PreservesFiniteLimits (Opens.map f.base) := by
    change PreservesFiniteLimits (OrderHom.ofClass f.base.frameHom).toFunctor
    infer_instance
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AffinePrincipal.Products
