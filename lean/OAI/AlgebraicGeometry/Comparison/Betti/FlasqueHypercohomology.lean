import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueConstantExt
import OAI.AlgebraicGeometry.Comparison.Betti.Acyclic.LinearHomDerived

/-! # Flasque Hypercohomology -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.FlasqueHypercohomology

noncomputable section

/-! Actual global sections compute hypercohomology of bounded-below flasque complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.TopologicalSpace Opposite

variable {X : TopCat.{0}}

local instance flasqueHypercohomologyExt : HasExt.{1} (ConstantSheafSections.ComplexSheaves X) := HasExt.standard _
local instance flasqueHypercohomologyDerived : HasDerivedCategory.{1} (ConstantSheafSections.ComplexSheaves X) :=
  HasDerivedCategory.standard _

def integerGlobalSectionsComplex (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ) :
    CochainComplex (ModuleCat.{0} ℂ) ℤ :=
  ((FlasqueBiproduct.sections (⊤ : Opens X)).mapHomologicalComplex (.up ℤ)).obj K

def integerConstantHomSectionsIso (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ) :
    LinearHomForget.Ext.integerLinearHomComplex (R := ℂ) (ConstantSheafSections.standardConstantSheaf X) K ≅
      integerGlobalSectionsComplex K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (ConstantSheafSections.constantHomSectionsLinearEquiv (K.X n)).toModuleIso)
    (fun i j _ => by
      ext f
      exact ConstantSheafSections.constantHomSectionsLinearEquiv_naturality f (K.d i j))

def flasqueHypercohomologyEquiv (K : CochainComplex (ConstantSheafSections.ComplexSheaves X) ℤ)
    (b : ℤ) [K.IsStrictlyGE b] (hK : ∀ p, TopCat.Sheaf.IsFlasque (K.X p)) (n : ℤ) :
    (integerGlobalSectionsComplex K).homology n ≃ₗ[ℂ]
      ((DerivedCategory.singleFunctor (ConstantSheafSections.ComplexSheaves X) 0).obj
        (ConstantSheafSections.standardConstantSheaf X) ⟶ (DerivedCategory.Q.obj K)⟦n⟧) := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℂ) (.up ℤ) n).mapIso
    (integerConstantHomSectionsIso K).symm
  refine e.toLinearEquiv.trans
    (Acyclic.LinearHomDerived.Ext.acyclicLinearHomCohomologyDerivedEquiv (ConstantSheafSections.standardConstantSheaf X) K b ?_ n)
  intro p q
  have := hK p
  exact FlasqueConstantExt.flasqueConstantExt_subsingleton (K.X p) q

end

end OAI.AlgebraicGeometry.Comparison.Betti.FlasqueHypercohomology
