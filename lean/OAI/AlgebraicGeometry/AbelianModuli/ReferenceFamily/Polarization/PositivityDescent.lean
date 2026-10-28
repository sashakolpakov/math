import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CartesianPolarizationFiberMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PositiveLineFormulaTransport
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Positivity Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PositivityDescent

noncomputable section

/-! Positivity descends from the original polarized family through
its actual etale cover, native group comparisons, and recovered Poincare line. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S Y : Scheme.{0}} {g h : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g Y} (D : HilbertConstruction.Dual.Data.DualAbelianData A)
    {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S} (E : HilbertConstruction.Dual.Data.DualAbelianData B) (u : Y ⟶ S)
    (eA : A.scheme ≅ (B.pullback u).scheme)
    (eD : D.abelian.scheme ≅ (E.abelian.pullback u).scheme)
    (p : A.scheme ⟶ D.abelian.scheme) (w : B.scheme ⟶ E.abelian.scheme)
    (hc : eA.hom ≫ (Over.pullback u).map w = p ≫ eD.hom)
    (hP : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartesianMixedProduct.CartesianFamily.mixedMap u eD eA) (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)

include hc hP in
theorem polarizationBiextensionClass_cartesian {T : Scheme.{0}} (s : T ⟶ Y) :
    let a := (CartesianFiberComparison.CartesianFamily.fiberComparison u A B eA s).hom
    Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (a ⊗ₘ a).left (HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.PolarizationData.polarizationBiextensionAt E w (s ≫ u))) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf (HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) := by
  let a := (CartesianFiberComparison.CartesianFamily.fiberComparison u A B eA s).hom
  exact (PicardSquareComparison.picardPullback_square (a ⊗ₘ a).left (HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap E w (s ≫ u))
    (HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s) (CartesianMixedProduct.CartesianFamily.mixedMap u eD eA)
    (CartesianPolarizationFiberMap.polarizationBiextensionMap_cartesian D E u eA eD p w hc s) (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare)).trans
      (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s)) hP)

include hc hP in
theorem positiveOnGeometricFiber_cartesian [IsMonHom eA.hom]
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y)
    (hp : HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s) : HilbertConstruction.PolarizationData.PositiveOnGeometricFiber E w K (s ≫ u) := by
  let e := CartesianFiberComparison.CartesianFamily.fiberComparison u A B eA s
  have : IsMonHom e.hom := CartesianFiberComparison.CartesianFamily.fiberComparison_isMonHom u A B eA s
  apply (PositiveLineOn.positiveOnGeometricFiber_iff_formula B E w K (s ≫ u)).mpr
  exact PositiveLineFormulaTransport.positiveLineFormula_transport (A.pullback s) (B.pullback (s ≫ u)) e
    (HilbertConstruction.PolarizationData.polarizationBiextensionAt D p s) (HilbertConstruction.PolarizationData.polarizationBiextensionAt E w (s ≫ u))
    (polarizationBiextensionClass_cartesian D E u eA eD p w hc hP s)
    ((PositiveLineOn.positiveOnGeometricFiber_iff_formula A D p K s).mp hp)

include hc hP in
theorem positiveOnGeometricFibers_of_etale_recovery [IsMonHom eA.hom] [Etale u] [Surjective u]
    (hp : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ Y), HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p K s) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S), HilbertConstruction.PolarizationData.PositiveOnGeometricFiber E w K s := by
  intro K _ _ s
  obtain ⟨x, hx⟩ := u.surjective (s default)
  obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed u s x hx
  have hpos := positiveOnGeometricFiber_cartesian D E u eA eD p w hc hP K l (hp K l)
  exact hl ▸ hpos

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarization.PositivityDescent
