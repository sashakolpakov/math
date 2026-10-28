import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.DiagonalPowerRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.ClassPairing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.ClassPowers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.Fibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingClass
import OAI.AlgebraicGeometry.Picard.PoincareBundle.InducingMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PositiveFormula

/-! # Symmetric Graph Inducing Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphInducingFormula

noncomputable section

/-! The actual graph line of a symmetric Poincaré pairing induces twice
the original homomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u

section Formula
variable {K : Type u} [Field K] {g : ℕ}
  {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
  (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]

theorem poincareGraph_inducingFormula_double
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x) :
    Nonempty (Tensor.ProductSheaf.tensorModule
      (Tensor.ProductSheaf.tensorModule (D.poincareAt (p ^ 2)).sheaf
        ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (fst A.scheme A.scheme).left).sheaf)
      ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback (snd A.scheme A.scheme).left).sheaf ≅
        ((PoincareGraph.Bundles.poincareGraphBundle D p).pullback μ[A.scheme].left).sheaf) := by
  let Q := PoincareGraph.Bundles.poincareGraphBundle D p
  let x := fst A.scheme A.scheme
  let y := snd A.scheme A.scheme
  let c : Line.Bundles.LineBundle.IsoClass (A.scheme ⊗ A.scheme).left :=
    Line.Bundles.LineBundle.classOf (D.poincareAt p)
  have hxy : x * y = μ[A.scheme] := by
    change (fst A.scheme A.scheme) * (snd A.scheme A.scheme) = μ[A.scheme]
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have hb := Bilinear.DiagonalPowerRecovery.symmetric_bilinear_diagonal_product
    (Polarization.ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme)) hs x y
  rw [hxy] at hb
  have hd : Line.Bundles.LineBundle.classOf (Q.pullback μ[A.scheme].left) =
      Line.Bundles.LineBundle.classOf (Q.pullback x.left) * Line.Bundles.LineBundle.classOf (Q.pullback y.left) *
        c ^ 2 := by
    calc
      _ = Polarization.ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme) μ[A.scheme] μ[A.scheme] :=
        Polarization.ClassPairing.graphPullback_class_eq_pair D p μ[A.scheme]
      _ = Polarization.ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme) x x *
          Polarization.ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme) y y *
          Polarization.ClassPairing.polarizationPairClass D p (A.scheme ⊗ A.scheme) x y ^ 2 := hb
      _ = _ := by
        rw [← Polarization.ClassPairing.graphPullback_class_eq_pair D p x,
          ← Polarization.ClassPairing.graphPullback_class_eq_pair D p y,
          ← Polarization.ClassPairing.poincareAt_class_eq_pair_projections D p]
        rfl
  let F : Line.Bundles.LineBundle (A.scheme ⊗ A.scheme).left := D.poincareAt (p ^ 2)
  have hF : Line.Bundles.LineBundle.classOf F = c ^ 2 := D.poincareAt_class_pow A.scheme p 2
  have hc : Line.Bundles.LineBundle.classOf ((F.tensor
      (Q.pullback x.left)).tensor (Q.pullback y.left)) =
      Line.Bundles.LineBundle.classOf (Q.pullback μ[A.scheme].left) := by
    rw [Line.Bundles.LineBundle.classOf_tensor, Line.Bundles.LineBundle.classOf_tensor, hF, hd]
    ac_rfl
  exact Quotient.exact hc

theorem poincareGraph_differenceClass_double
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x) :
    Picard.PoincareBundle.InducingClass.Bundle.lineClass A.scheme (PoincareGraph.Bundles.poincareGraphBundle D p) =
      Line.Bundles.LineBundle.classOf (D.poincareAt (p ^ 2)) := by
  obtain ⟨e⟩ := poincareGraph_inducingFormula_double D p hs
  exact (Picard.PoincareBundle.InducingClass.Bundle.class_eq_of_formula A.scheme
    (PoincareGraph.Bundles.poincareGraphBundle D p) (D.poincareAt (p ^ 2)) e).symm

theorem poincareGraph_positiveFormula_double
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x)
    (hQ : (PoincareGraph.Bundles.poincareGraphBundle D p).IsAmple) :
    AbelianScheme.IsogenyQuotient.PositiveFormula.Construction.PositivePoincareFormula A.scheme (D.poincareAt (p ^ 2)) :=
  ⟨PoincareGraph.Bundles.poincareGraphBundle D p, hQ, ⟨PoincareGraph.Fibers.poincareGraphBundle_zeroIso D p⟩,
    poincareGraph_inducingFormula_double D p hs⟩
end Formula

variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}
  {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)

theorem inducingPicardMap_eq_of_formula
    (L : Line.Bundles.LineBundle A.scheme.left) (q : A.scheme ⟶ D.abelian.scheme)
    (o : (L.pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule (Spec (.of K)))
    (e : (((D.poincareAt q).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf) :
    Picard.PoincareBundle.InducingMap.hom D L = q := by
  obtain ⟨c⟩ := Picard.PoincareBundle.InducingMap.exists_familyIso D L o
  rw [tensorHom_id] at c
  have hc : Line.Bundles.LineBundle.classOf (D.poincareAt (Picard.PoincareBundle.InducingMap.hom D L)) =
      Line.Bundles.LineBundle.classOf (Picard.PoincareBundle.InducingClass.Bundle.line A.scheme L) :=
    Quotient.sound ⟨c.symm⟩
  apply D.poincareAt_class_injective A.scheme
  exact hc.trans ((Picard.PoincareBundle.InducingClass.Bundle.classOf_line A.scheme L).trans
    (Picard.PoincareBundle.InducingClass.Bundle.class_eq_of_formula A.scheme L (D.poincareAt q) e).symm)

theorem poincareGraph_inducingPicardMap_double
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
    (hs : ∀ x y : A.scheme ⊗ A.scheme ⟶ A.scheme,
      D.poincarePairClass (A.scheme ⊗ A.scheme) (x ≫ p) y =
        D.poincarePairClass (A.scheme ⊗ A.scheme) (y ≫ p) x) :
    Picard.PoincareBundle.InducingMap.hom D (PoincareGraph.Bundles.poincareGraphBundle D p) = p ^ 2 := by
  obtain ⟨e⟩ := poincareGraph_inducingFormula_double D p hs
  exact inducingPicardMap_eq_of_formula D (PoincareGraph.Bundles.poincareGraphBundle D p) (p ^ 2)
    (PoincareGraph.Fibers.poincareGraphBundle_zeroIso D p) e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SymmetricGraphInducingFormula
