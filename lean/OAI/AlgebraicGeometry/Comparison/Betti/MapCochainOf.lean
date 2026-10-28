import Mathlib.Algebra.Homology.Additive

/-! # Map Cochain Of -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.MapCochainOf.Complex

noncomputable section

/-! Mapping a cochain complex given by successive differentials preserves that presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms]
  (X : ℕ → C) (d : ∀ n, X n ⟶ X (n + 1)) (w : ∀ n, d n ≫ d (n + 1) = 0)

def mapCochainOfIso :
    (F.mapHomologicalComplex (.up ℕ)).obj (CochainComplex.of X d w) ≅
      CochainComplex.of (fun n => F.obj (X n)) (fun n => F.map (d n))
        (fun n => by rw [← F.map_comp, w n, F.map_zero]) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ CochainComplex.of.d (fun k => F.obj (X k)) (fun k => F.map (d k)) i (i + 1) =
      F.map (CochainComplex.of.d X d i (i + 1)) ≫ 𝟙 _
    rw [CochainComplex.of_d, CochainComplex.of_d, Category.id_comp, Category.comp_id])

end

end OAI.AlgebraicGeometry.Comparison.Betti.MapCochainOf.Complex
