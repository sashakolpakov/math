import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.BaseHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyCompose
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-! # Homology Presheaf -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf

noncomputable section

/-! The actual homology presheaf compares canonically with the original homology sheaf on affine opens. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

universe u

variable (k : Type u) [CommRing k] (X : Over (Spec (CommRingCat.of k)))

def functor : X.left.Modules ⥤ X.left.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  AlgebraSheafScalars.functor k X ⋙ sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{u} k)

instance additive : (functor k X).Additive where
  map_add := rfl

instance preservesFiniteLimits : PreservesFiniteLimits (functor k X) := by
  apply preservesFiniteLimits_of_evaluation
  intro U
  exact BaseHomology.preservesFiniteLimits k X U.unop

variable (S : ShortComplex X.left.Modules)

def map : (S.map (functor k X)).homology ⟶ (functor k X).obj S.homology :=
  LeftExactHomology.Comparison.map (functor k X) S

theorem affine_isIso [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (U : X.left.Opens) (hU : IsAffineOpen U) : IsIso ((HomologyPresheaf.map k X S).app (op U)) := by
  let G := (CategoryTheory.evaluation X.left.Opensᵒᵖ (ModuleCat.{u} k)).obj (op U)
  have : ((functor k X) ⋙ G).PreservesLeftHomologyOf S :=
    BaseHomology.preservesLeft k X U hU S
  exact HomologyCompose.Comparison.isIso_map (functor k X) G S

theorem naturality {T : ShortComplex X.left.Modules} (φ : S ⟶ T) :
    ShortComplex.homologyMap ((functor k X).mapShortComplex.map φ) ≫ HomologyPresheaf.map k X T =
      HomologyPresheaf.map k X S ≫ (functor k X).map (ShortComplex.homologyMap φ) :=
  LeftExactHomology.Comparison.naturality (functor k X) φ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.HomologyPresheaf
