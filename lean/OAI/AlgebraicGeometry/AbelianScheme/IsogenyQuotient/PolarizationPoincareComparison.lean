import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polarizations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Polarization Poincare Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction

noncomputable section

/-!
The fixed-dimension HilbertConstruction polarization and the dimension-independent CartierDuality
polarization use the same original Poincare bundle and geometric
ampleness condition. Their iterated line-bundle pullbacks are compared
by the actual canonical pullback isomorphisms.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)

def nativeAbelianOfHilbertConstruction : Picard.Homomorphisms.AbelianSchemes.Construction.AbelianScheme S where
  toOver := A.scheme
  group := A.group
  commutative := A.commutative
  proper := A.proper
  smooth := inferInstance
  connected := A.connected

variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPoincarePullbackMap_ofHilbertConstruction {T : Scheme.{u}} (s : T ⟶ S) :
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.poincarePullbackOverMap s).left =
      AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D s :=
  (AbelianModuli.HilbertConstruction.Pullback.Comparisons.poincareBaseChangeMap_eq_pullbackOverMap D s).symm

set_option backward.isDefEq.respectTransparency false in
def canonicalPolarizationBiextensionIso_ofHilbertConstruction
    (p : A.scheme ⟶ D.abelian.scheme) {T : Scheme.{u}} (s : T ⟶ S) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (((Over.pullback s).map p ⊗ₘ 𝟙 ((Over.pullback s).obj A.scheme)).left)
      (((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.pullback s).poincare)).sheaf ≅
      (AbelianModuli.HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s).sheaf := by
  let a := ((Over.pullback s).map p ⊗ₘ 𝟙 ((Over.pullback s).obj A.scheme)).left
  let c := ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup.poincarePullbackOverMap s).left
  exact (Scheme.Modules.pullbackComp a c).app D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg (fun z => a ≫ z) (canonicalPoincarePullbackMap_ofHilbertConstruction A D s))).app D.poincare.sheaf

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPositiveOnGeometricFiber_ofHilbertConstruction
    (p : A.scheme ⟶ D.abelian.scheme)
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S)
    (hp : AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p k s) :
    Picard.Homomorphisms.Polarizations.Construction.PositiveOnGeometricFiber (nativeAbelianOfHilbertConstruction A)
      (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).withPicardGroup p k s := by
  obtain ⟨L, hL, hzero, ⟨hformula⟩⟩ := hp
  refine ⟨L, hL, hzero, ⟨?_⟩⟩
  exact AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (canonicalPolarizationBiextensionIso_ofHilbertConstruction A D p s) (Iso.refl _))
      (Iso.refl _) ≪≫ hformula

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PolarizationPoincareComparison.Construction
