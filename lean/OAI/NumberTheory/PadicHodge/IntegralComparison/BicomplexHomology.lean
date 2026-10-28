import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Bicomplex Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHomology

noncomputable section

/-! The actual homology complex of a bicomplex agrees with row homology after flipping. -/

open _root_.CategoryTheory Limits

variable {A : Type*} [Category* A] [Abelian A]
  (K : HomologicalComplex₂ A (.up ℕ) (.up ℕ))

def rows (p : ℕ) : CochainComplex A ℕ :=
  ((HomologicalComplex.homologyFunctor A (.up ℕ) p).mapHomologicalComplex (.up ℕ)).obj K.flip

def component (p q : ℕ) : (rows K p).X q ≅ (K.homology p).X q :=
  (K.sc p).mapHomologyIso (HomologicalComplex.eval A (.up ℕ) q)

theorem component_d (p q r : ℕ) :
    (component K p q).hom ≫ (K.homology p).d q r = (rows K p).d q r ≫ (component K p r).hom := by
  let S := K.sc p
  let τ := HomologicalComplex.dNatTrans A (.up ℕ) q r
  have h := S.homologyMap_mapNatTrans τ
  change (S.mapHomologyIso (HomologicalComplex.eval A (.up ℕ) q)).hom ≫ τ.app S.homology =
    ShortComplex.homologyMap (S.mapNatTrans τ) ≫
      (S.mapHomologyIso (HomologicalComplex.eval A (.up ℕ) r)).hom
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

def iso (p : ℕ) : rows K p ≅ K.homology p :=
  HomologicalComplex.Hom.isoOfComponents (component K p) (fun q r _ => component_d K p q r)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexHomology
