import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.Koszul
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalReference.Concentration

/-! # Intrinsic Dual Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.IntrinsicDualCoordinates.Intrinsic

noncomputable section

/-! The original principal internal-Hom complex and principal sections
of the original sheaf dual complex have identical coordinates. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
universe u
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)
  (N : X.Modules) (K : ChainComplex X.Modules ℕ)

def sourceIso : Koszul.Comparison.nativeComplex U hU N K ≅
    ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj
      (Affine.LinearResolutionPurity.internalComplex N K) := Iso.refl _

variable {L : CochainComplex ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat Γ(X,U)) ℕ}

def map (a : Koszul.Comparison.nativeComplex U hU N K ⟶ L) :
    ((ModuleFunctor.functor U hU).mapHomologicalComplex (.up ℕ)).obj
      (Affine.LinearResolutionPurity.internalComplex N K) ⟶ L := a

theorem map_eq (a : Koszul.Comparison.nativeComplex U hU N K ⟶ L) :
    map U hU N K a = (sourceIso U hU N K).inv ≫ a := by
  change a = 𝟙 _ ≫ a
  exact (Category.id_comp a).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.IntrinsicDualCoordinates.Intrinsic
