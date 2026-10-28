import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes

/-! # Inducing Class -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle

noncomputable section

/-! The actual line determined by the inducing formula, and its compatibility with group-homomorphism pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemePullback.Construction

variable {S : Scheme.{u}} (A : Over S) [GrpObj A]

/-- The difference between multiplication pullback and the two projection pullbacks. -/
def lineClass (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A ⊗ A).left :=
  Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)

/-- An actual locally free rank-one sheaf representing this difference. -/
def line (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left := (lineClass A L).out

theorem classOf_line (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (line A L) = lineClass A L :=
  Quotient.out_eq _

/-- The constructed line has an actual inducing formula. -/
def formula (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (line A L).sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (line A L) * Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
    rw [classOf_line]
    simp [lineClass, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  exact Classical.choice (Quotient.exact h)

/-- Any actual inducing formula identifies its line with the constructed difference class. -/
theorem class_eq_of_formula (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (Q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (A ⊗ A).left)
    (e : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule Q.sheaf (L.pullback (fst A A).left).sheaf)
      (L.pullback (snd A A).left).sheaf ≅ (L.pullback μ[A].left).sheaf) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q = lineClass A L := by
  have h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf Q * Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
        Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := Quotient.sound ⟨e⟩
  rw [lineClass, div_div]
  exact (eq_div_iff_mul_eq').mpr ((mul_assoc _ _ _).symm.trans h)

/-- Evaluation on arbitrary scheme-valued pairs is the corresponding difference of fiber classes. -/
theorem lineClass_atPoint (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over S} (a b : T ⟶ A) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a b).left (lineClass A L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback (a * b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
        Homomorphisms.SchemePullback.Construction.schemePicardPullback a.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) /
        Homomorphisms.SchemePullback.Construction.schemePicardPullback b.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
  rw [lineClass, map_div, map_div]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) /
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) /
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (lift a b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  have h1 := congrArg Over.Hom.left (lift_fst a b)
  have h2 := congrArg Over.Hom.left (lift_snd a b)
  change (lift a b).left ≫ (fst A A).left = a.left at h1
  change (lift a b).left ≫ (snd A A).left = b.left at h2
  rw [h1, h2]
  rfl

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass.Bundle
