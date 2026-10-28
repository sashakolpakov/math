import OAI.AlgebraicGeometry.Comparison.Betti.Godement.GlobalNormalization

/-! # Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Cech.Hypercohomology

noncomputable section

/-! A finite cover acyclic for every term computes the original derived hypercohomology of a nonnegative complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Godement.GlobalNormalization

variable {X : TopCat.{0}} {ι : Type} [Finite ι] (U : ι → Opens X)
  (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℕ)

local instance cechHypercohomologyDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves X) :=
  HasDerivedCategory.standard _

def cechHypercohomologyEquiv (hU : ⨆ i, U i = ⊤)
    (hK : ∀ r, SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := X) U
      ((Complex.SheafForget.Flasque.sheafForget X).obj (K.X r))) (n : ℕ) :
    ((FlasqueCechTotal.additiveSheafSectionCechBicomplex U (Godement.Cech.additiveGodementComplex K)).total (.up ℕ)).homology n ≃+
      ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves X) 0).obj
        (ConstantSheafSections.standardConstantSheaf X) ⟶
          (DerivedCategory.Q.obj (K.extend (ComplexShape.embeddingUpIntGE 0)))⟦(n : ℤ)⟧) :=
  (Godement.Cech.godementCechHomologyIso U K hU hK n).addCommGroupIsoToAddEquiv.trans
    ((Godement.GlobalNormalization.additiveGlobalForgetHomologyEquiv (Godement.Bicomplex.godementTotal K) n).trans
      ((Godement.GlobalNormalization.natSectionsIntHomologyIso (Godement.Bicomplex.godementTotal K) n).toLinearEquiv.toAddEquiv.trans
        (Godement.Hypercohomology.godementHypercohomologyEquiv K (n : ℤ)).toAddEquiv))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Cech.Hypercohomology
