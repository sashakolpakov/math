import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianMixedProduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.Transport

/-! # Cartesian Polarized Level Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery

noncomputable section

/-! The native recovered group, dual, Poincare, polarization, and full
level equations construct an actual isomorphism in the original moduli problem. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

theorem mixedMap_poincareFactor {S Y : Scheme.{0}} {g : ℕ} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData B) (u : Y ⟶ S) {A E : Over Y}
    (eA : A ≅ (B.pullback u).scheme) (eD : E ≅ (D.abelian.pullback u).scheme) :
    CartesianMixedProduct.CartesianFamily.mixedMap u eD eA = (eD.hom ⊗ₘ eA.hom).left ≫ (D.poincarePullbackOverMap u).left := by
  have h : CartesianMixedProduct.CartesianFamily.mixedMap u eD eA = (eD.hom ⊗ₘ eA.hom).left ≫ HilbertConstruction.PolarizationData.poincareBaseChangeMap D u :=
    Category.assoc (eD.hom ⊗ₘ eA.hom).left
      (Functor.Monoidal.μIso (Over.pullback u) D.abelian.scheme B.scheme).hom.left
      (pullback.fst (D.abelian.scheme ⊗ B.scheme).hom u)
  exact h.trans (congrArg (fun f => (eD.hom ⊗ₘ eA.hom).left ≫ f) (HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D u))

def levelIso_of_cartesian_recovery {S Y : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Y) (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (u : Y ⟶ S)
    (eA : A.abelian.scheme ≅ (B.abelian.pullback u).scheme)
    (eD : A.dual.abelian.scheme ≅ (B.dual.abelian.pullback u).scheme)
    [IsMonHom eA.hom] [IsMonHom eD.hom]
    (hp : eA.hom ≫ (Over.pullback u).map B.polarization.isogeny.hom = A.polarization.isogeny.hom ≫ eD.hom)
    (hP : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartesianMixedProduct.CartesianFamily.mixedMap u eD eA) (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare)
    (hL : B.level.pullback u = A.level.transport eA) : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A (B.pullback u) where
  abelian := eA
  dual := eD
  abelianGroup := inferInstanceAs (IsMonHom eA.hom)
  dualGroup := inferInstanceAs (IsMonHom eD.hom)
  polarization := hp.symm
  poincare :=
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (eD.hom ⊗ₘ eA.hom).left (B.dual.poincarePullbackOverMap u).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare)).symm.trans
      ((congrArg (fun f => HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare))
        (mixedMap_poincareFactor B.dual u eA eD).symm).trans hP)
  level T c :=
    (A.level.transport_basis eA T c).symm.trans
      (congrArg (fun α : (B.abelian.pullback u).FullLevel N => (α.hom.app (.op T) c).val) hL.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizedLevelRecovery
