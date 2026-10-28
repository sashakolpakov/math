import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses

/-! # Diagonal Line Class -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass

noncomputable section

/-! The Poincare diagonal equals the actual symmetrization of an inducing line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.LineClasses OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {A D : Over S}
  (P : Line.Bundles.LineBundle (D ⊗ A).left) (ell : A ⟶ D)

/-- The actual line on the diagonal of the pulled Poincare family. -/
def diagonalLine : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left := (Line.Comparison.Bundle.toShared P).pullback (lift ell (𝟙 A)).left

/-- The class of the Poincare family induced by the original morphism. -/
def biextensionClass : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (A ⊗ A).left :=
  Homomorphisms.SchemePullback.Construction.schemePicardPullback (ell ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Line.Comparison.Bundle.toShared P))

/-- Evaluation agrees with the class at the two actual scheme-valued points. -/
theorem biextensionClass_evaluate {T : Over S} (a b : T ⟶ A) :
    Homomorphisms.SchemePullback.Construction.schemePicardPullback (lift a b).left (biextensionClass P ell) = Poincare.LineClasses.pairClass P (a ≫ ell) b := by
  have h : (lift a b).left ≫ (ell ⊗ₘ 𝟙 A).left = (lift (a ≫ ell) b).left := by
    simpa only [Category.comp_id, Over.comp_left] using
      congrArg Over.Hom.left (lift_map a b ell (𝟙 A))
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (lift a b).left (ell ⊗ₘ 𝟙 A).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Line.Comparison.Bundle.toShared P))).symm.trans
    (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (Line.Comparison.Bundle.toShared P))) h)

variable [GrpObj A] (Dv : FiberwiseMultiplication.Multiplication (snd D A) (fst D A) P)

include Dv

theorem diagonalLine_symmetrization (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left)
    (hzero : Homomorphisms.SchemePullback.Construction.schemePicardPullback (1 : A ⟶ A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = 1)
    (hFormula : biextensionClass P ell *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) *
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (diagonalLine P ell) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.tensor (L.pullback (GrpObj.inv (X := A)).left)) := by
  let z := lift (𝟙 A) (GrpObj.inv (X := A))
  have hf : z.left ≫ (fst A A).left = 𝟙 A.left :=
    congrArg Over.Hom.left (lift_fst (𝟙 A) (GrpObj.inv (X := A)))
  have hs : z.left ≫ (snd A A).left = (GrpObj.inv (X := A)).left :=
    congrArg Over.Hom.left (lift_snd (𝟙 A) (GrpObj.inv (X := A)))
  have hm : z.left ≫ μ[A].left = (1 : A ⟶ A).left := by
    have he : z ≫ μ[A] = 1 := by
      change (𝟙 A) * (GrpObj.inv (X := A)) = 1
      rw [GrpObj.inv_eq_inv, mul_inv_cancel]
    exact congrArg Over.Hom.left he
  have h := congrArg (Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left) hFormula
  rw [map_mul, map_mul] at h
  have hp : Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left (biextensionClass P ell) =
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (diagonalLine P ell))⁻¹ := by
    have h₀ := biextensionClass_evaluate P ell (𝟙 A) (GrpObj.inv (X := A))
    rw [Category.id_comp, GrpObj.inv_eq_inv, Poincare.LineClasses.pairClass_inv_right P Dv] at h₀
    exact h₀
  have pbf : Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Homomorphisms.SchemePullback.Construction.schemePicardPullback (fst A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left (fst A A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hf).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)))
  have pbs : Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Homomorphisms.SchemePullback.Construction.schemePicardPullback (snd A A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
        Homomorphisms.SchemePullback.Construction.schemePicardPullback (GrpObj.inv (X := A)).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left (snd A A).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      (congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hs)
  have pbm : Homomorphisms.SchemePullback.Construction.schemePicardPullback z.left
      (Homomorphisms.SchemePullback.Construction.schemePicardPullback μ[A].left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = 1 := by
    exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp z.left μ[A].left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun f => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) hm).trans hzero)
  rw [hp, pbf, pbs, pbm, mul_assoc] at h
  exact inv_mul_eq_one.mp h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.DiagonalLineClass
