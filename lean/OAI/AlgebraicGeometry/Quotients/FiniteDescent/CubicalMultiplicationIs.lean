import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.FromPowerSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPowersAdd
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalAlgebraPow

/-! # Cubical Multiplication Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication

noncomputable section

/-! Multiplication finiteness from the geometric cube identity. The cube
identity remains an explicit input; no ample bundle or polarization is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {K : Type u} [Field K]
variable (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]

def pullbackClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (a : A ⟶ A) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)

/-- The cube identity expressed by pulling back a line bundle along three
endomorphisms of the underlying scheme over the field. -/
def IsCubical (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : Prop :=
  ∀ a b c : A ⟶ A,
    pullbackClass A L (a * b * c) * pullbackClass A L a *
        pullbackClass A L b * pullbackClass A L c =
      pullbackClass A L (a * b) * pullbackClass A L (a * c) * pullbackClass A L (b * c)

theorem class_one (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : pullbackClass A L 1 = 1 := by
  have hone : (1 : A ⟶ A).left = A.hom ≫ (MonObj.one (X := A)).left := rfl
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (1 : A ⟶ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1
  rw [hone, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (MonObj.one (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Spec (.of K)) :=
    Quotient.sound (LineTrivializationOf.Construction.LineTrivialization.pullback_trivial_over_field (MonObj.one (X := A)).left L)
  rw [hp, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  rfl

theorem class_inv (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (a : A ⟶ A) : pullbackClass A L a⁻¹ = pullbackClass A L a := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (a.left ≫ (GrpObj.inv (X := A)).left) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = _
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := Quotient.sound hsym
  rw [h]
  rfl

/-- The symmetric cube identity gives the actual `n²` tensor-power isomorphism. -/
theorem power_iso (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hsym : Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf))
    (hcube : IsCubical A L) (n : ℕ) :
    Nonempty ((L.tensorPower (n * n)).sheaf ≅ (L.pullback ((𝟙 A : A ⟶ A) ^ n).left).sheaf) := by
  have h := CubicalAlgebraPow.Construction.CubicalAlgebra.pow (pullbackClass A L) (class_one A L) (class_inv A L hsym)
    hcube (𝟙 A) n
  have hid : pullbackClass A L (𝟙 A) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L :=
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id _
  rw [hid] at h
  have heq : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensorPower (n * n)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 A : A ⟶ A) ^ n).left) :=
    (PicardPowersAdd.Construction.PicardPowers.class_pow L (n * n)).trans h.symm
  exact Quotient.exact heq

/-- The geometric cube identity alone now suffices for multiplication finiteness:
the needed affine section neighborhoods have already been constructed. -/
theorem isFinite [IsAlgClosed K] [IsProper A.hom] [Smooth A.hom]
    [GeometricallyConnected A.hom] (hcube : ∀ L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left, IsCubical A L)
    (n : ℕ) (hn : 0 < n) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  let f := ((𝟙 A : A ⟶ A) ^ n).left
  have : IsProper (f ≫ A.hom) := by rw [Over.w]; infer_instance
  have : IsProper f := IsProper.of_comp f A.hom
  apply FromPowerSections.Construction.FiniteFromPowerSections.isFinite f
  intro x
  obtain ⟨L, s, hx, hs, hsym⟩ := SymmetricAffine.Construction.SymmetricAffineSections.exists_for_group A x
  exact ⟨L, L, n * n, Nat.mul_pos hn hn, power_iso A L hsym (hcube L) n, s, hx, hs⟩

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubicalMultiplicationIs.Construction.CubicalMultiplication
