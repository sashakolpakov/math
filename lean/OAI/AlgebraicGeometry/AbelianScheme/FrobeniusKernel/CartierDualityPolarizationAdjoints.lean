import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityWeilAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicTorsionSheafFunctor
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SheafPairingAdjoints

/-! # Cartier Duality Polarization Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints

noncomputable section

/-! Rosati squares imply adjoint actions for CartierDuality's actual polarization
pairing. No torsion pairing compatibility is added as a hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative

namespace Construction

variable {S : Scheme} (A : CartierDuality.PolarizedTorsion.AbelianScheme S) (ell : CartierDuality.PolarizedTorsion.Polarization A)

def e56PolarizationGroupHom : Grp.mk A.toOver ⟶ Grp.mk ell.dual.abelian :=
  @Grp.homMk (Over S) _ _ (Grp.mk A.toOver) (Grp.mk ell.dual.abelian)
    ell.map ell.preservesGroup

variable (n : ℕ) (hn : 0 < n) (p r : A.toOver ⟶ A.toOver) [IsMonHom p] [IsMonHom r]

theorem e56PolarizationPairing_adjoint
    (h : r ≫ ell.map = ell.map ≫ (IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.toOver p ell.dual).hom.hom) :
    CartierDuality.PolarizedTorsion.ProjectorsAdjoint (CartierDuality.PolarizedTorsion.Polarization.torsionPairing ell n hn)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.toOver p)) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.toOver r)) n) := by
  let a := IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.toOver r
  let b := IntrinsicCartierNaturality.Construction.nativePicardEndomorphismGroup A.toOver p ell.dual
  let f := e56PolarizationGroupHom A ell
  have hgroup : a ≫ f = f ≫ b := by
    apply Grp.hom_ext
    exact h
  have hrep : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a f).symm.trans
      ((congrArg (fun t => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap t) hgroup).trans (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp f b))
  exact SheafPairingAdjoints.Construction.pairing_restrict_right_adjoint (CartierDuality.PolarizedTorsion.Polarization.weilPairing ell n hn) _ _
    (CartierDualityWeilAdjoints.Construction.e56WeilPairing_endomorphism A ell n hn p) (CartierDuality.PolarizedTorsion.Polarization.torsionMap ell n) _
    (IntrinsicTorsionSheafFunctor.Construction.torsionSheafMap_square _ _ _ _ hrep n)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CartierDualityPolarizationAdjoints
