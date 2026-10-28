import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PositiveFormula
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Reference.PairingIndependence

/-! # Polarization Torsion Pairing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing

noncomputable section

/-! The original polarization supplies all the line, product and symmetry data in its full torsion pairing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

variable {k : Type} [Field k] [IsAlgClosed k] {a : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin a → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ)

/-- An actual ample inducing line, obtained from the given polarization's geometric positivity. -/
def inducingLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left :=
  Classical.choose (Reference.PositiveFormula.of_polarization D pol)

theorem inducingLine_ample : (inducingLine D pol).IsAmple :=
  (Classical.choose_spec (Reference.PositiveFormula.of_polarization D pol)).1

theorem inducingLine_zero : Nonempty (((inducingLine D pol).pullback η[A.scheme].left).sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of k))) :=
  (Classical.choose_spec (Reference.PositiveFormula.of_polarization D pol)).2.1

theorem inducingLine_formula : Nonempty (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (FirstBiextensionFactor.familyLine (Line.Comparison.Bundle.fromShared D.poincare) pol.isogeny.hom).sheaf
      ((inducingLine D pol).pullback (fst A.scheme A.scheme).left).sheaf)
    ((inducingLine D pol).pullback (snd A.scheme A.scheme).left).sheaf ≅
      ((inducingLine D pol).pullback μ[A.scheme].left).sheaf) :=
  (Classical.choose_spec (Reference.PositiveFormula.of_polarization D pol)).2.2

attribute [local instance] Kernel.Scheme.kernelGroup

/-- The full canonical torsion pairing needs only the original polarization and the integer. -/
def pairing (n : ℕ) (T : Over (Spec (.of k))) :
    (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) →*
      (T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) →* Γ(T.left, ⊤)ˣ :=
  Reference.PairingIndependence.ReferenceTorsion.pairing D pol.isogeny.hom (inducingLine D pol) (inducingLine_formula D pol) n T

/-- The polarization's pairing retains naturality on all scheme-valued points. -/
theorem pairing_natural (n : ℕ) {T T' : Over (Spec (.of k))} (b : T' ⟶ T)
    (x y : T ⟶ Kernel.Scheme.kernelObject ((𝟙 A.scheme) ^ n)) :
    pairing D pol n T' (b ≫ x) (b ≫ y) =
      Units.map b.left.appTop.hom (pairing D pol n T x y) :=
  Reference.PairingIndependence.ReferenceTorsion.pairing_natural D pol.isogeny.hom (inducingLine D pol)
    (inducingLine_formula D pol) n b x y

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PolarizationTorsionPairing
