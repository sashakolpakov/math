import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleTensor

/-! # Line Bundle Classes -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleClasses

noncomputable section

/-! Frobenius and tensor powers on isomorphism classes of actual line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}}

/-- The n-th tensor power on line-bundle classes. -/
def tensorPowerClass (n : ℕ) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X → AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X :=
  Quotient.map (fun L => LineBundleTensor.Construction.tensorPowerLineBundle L n) (fun L M ⟨e⟩ =>
    ((TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf n).of_sourceIso e).unique
      (TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower M.sheaf n))

theorem tensorPowerClass_one (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) : tensorPowerClass 1 q = q := by
  induction q using Quotient.inductionOn with
  | h L =>
    exact Quotient.sound
      ((TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower L.sheaf 1).unique (AbelianModuli.HilbertConstruction.Tensor.Powers.isTensorPower_one L.sheaf))

theorem tensorPowerClass_trivial (n : ℕ) :
    tensorPowerClass n (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass X :=
  Quotient.sound ((TensorPowerSheaf.Construction.tensorPowerSheaf_isTensorPower (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) n).unique (UnitTensorPower.Construction.unit_isTensorPower X n))

theorem frobeniusPullbackClass_eq_tensorPowerClass
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass X) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Frobenius.Construction.absoluteFrobenius p hp X hX) q = tensorPowerClass p q := by
  induction q using Quotient.inductionOn with
  | h L => exact Quotient.sound ⟨LineBundleTensor.Construction.frobeniusPullbackLineBundleIso p hp hX L⟩

/-- Tensor p-th powers commute with arbitrary base change in characteristic p. -/
theorem tensorPowerClass_pullback
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    (f : X ⟶ Y) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass Y) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (tensorPowerClass p q) =
      tensorPowerClass p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f q) := by
  rw [← frobeniusPullbackClass_eq_tensorPowerClass p hp hY,
    ← frobeniusPullbackClass_eq_tensorPowerClass p hp hX,
    ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
    Frobenius.Construction.absoluteFrobenius_naturality p hp hX hY f]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleClasses
