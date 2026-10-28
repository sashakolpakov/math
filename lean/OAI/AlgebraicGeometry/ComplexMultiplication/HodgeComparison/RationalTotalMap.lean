import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns

/-! # Rational Total Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTotalMap.CM.Construction

noncomputable section

/-! Componentwise rational-linear maps into complex bicomplexes induce
actual maps into the scalar restriction of their native total complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive

variable (K : HomologicalComplex₂ (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  (L : HomologicalComplex₂ (ModuleCat.{0} ℂ) (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  (F : ∀ p q, (K.X p).X q ⟶ PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj ((L.X p).X q))

def rationalComplexTotalDegreeMap (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).X n ⟶ PositiveCohomologyConjugation.CM.Construction.restrictToRational.obj ((L.total (ComplexShape.up ℕ)).X n) :=
  K.totalDesc (fun p q h => F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map (L.ιTotal (ComplexShape.up ℕ) p q n h))

theorem rationalComplexTotalDegreeMap_iota (p q n : ℕ) (h : p + q = n) :
    K.ιTotal (ComplexShape.up ℕ) p q n h ≫ rationalComplexTotalDegreeMap K L F n =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map (L.ιTotal (ComplexShape.up ℕ) p q n h) :=
  K.ι_totalDesc _ p q h

theorem rationalComplexTotalDegreeMap_comm
    (hH : ∀ p q, (K.d p (p + 1)).f q ≫ F (p + 1) q =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.d p (p + 1)).f q))
    (hV : ∀ p q, (K.X p).d q (q + 1) ≫ F p (q + 1) =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.X p).d q (q + 1))) (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).d n (n + 1) ≫ rationalComplexTotalDegreeMap K L F (n + 1) =
      rationalComplexTotalDegreeMap K L F n ≫
        PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.total (ComplexShape.up ℕ)).d n (n + 1)) := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q h
  change p + q = n at h
  let iKH := K.ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) (show p + 1 + q = n + 1 by omega)
  let iKV := K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (show p + (q + 1) = n + 1 by omega)
  let iLH := L.ιTotal (ComplexShape.up ℕ) (p + 1) q (n + 1) (show p + 1 + q = n + 1 by omega)
  let iLV := L.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (show p + (q + 1) = n + 1 by omega)
  have hiK := AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.iota_d_of_eq K p q n h
  have hiL := AlgebraicTopology.DeRham.Comparison.DoubleComplexSigns.DoubleComplex.iota_d_of_eq L p q n h
  have hh : ((K.d p (p + 1)).f q ≫ iKH) ≫ rationalComplexTotalDegreeMap K L F (n + 1) =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.d p (p + 1)).f q ≫ iLH) := by
    change ((K.d p (p + 1)).f q ≫ K.ιTotal _ _ _ _ _) ≫ _ = _
    rw [Category.assoc, rationalComplexTotalDegreeMap_iota, ← Category.assoc, hH,
      Category.assoc, ← PositiveCohomologyConjugation.CM.Construction.restrictToRational.map_comp]
  have hv : ((K.X p).d q (q + 1) ≫ iKV) ≫ rationalComplexTotalDegreeMap K L F (n + 1) =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.X p).d q (q + 1) ≫ iLV) := by
    change ((K.X p).d q (q + 1) ≫ K.ιTotal _ _ _ _ _) ≫ _ = _
    rw [Category.assoc, rationalComplexTotalDegreeMap_iota, ← Category.assoc, hV,
      Category.assoc, ← PositiveCohomologyConjugation.CM.Construction.restrictToRational.map_comp]
  calc
    _ = ((K.d p (p + 1)).f q ≫ iKH + ((-1 : ℤ) ^ p) • ((K.X p).d q (q + 1) ≫ iKV)) ≫
        rationalComplexTotalDegreeMap K L F (n + 1) := by rw [← Category.assoc, hiK]
    _ = ((K.d p (p + 1)).f q ≫ iKH) ≫ rationalComplexTotalDegreeMap K L F (n + 1) +
        ((-1 : ℤ) ^ p) • (((K.X p).d q (q + 1) ≫ iKV) ≫ rationalComplexTotalDegreeMap K L F (n + 1)) := by
      rw [add_comp, zsmul_comp]
    _ = (F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.d p (p + 1)).f q ≫ iLH)) +
        ((-1 : ℤ) ^ p) • (F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.X p).d q (q + 1) ≫ iLV)) := by rw [hh, hv]
    _ = F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map
        ((L.d p (p + 1)).f q ≫ iLH + ((-1 : ℤ) ^ p) • ((L.X p).d q (q + 1) ≫ iLV)) := by
      rw [PositiveCohomologyConjugation.CM.Construction.restrictToRational.map_add, PositiveCohomologyConjugation.CM.Construction.restrictToRational.map_zsmul, comp_add, comp_zsmul]
    _ = F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map
        (L.ιTotal (ComplexShape.up ℕ) p q n h ≫ (L.total (ComplexShape.up ℕ)).d n (n + 1)) :=
      congrArg (fun g => F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map g) hiL.symm
    _ = _ := by
      rw [PositiveCohomologyConjugation.CM.Construction.restrictToRational.map_comp, ← Category.assoc, ← rationalComplexTotalDegreeMap_iota, Category.assoc]

def rationalComplexTotalMap
    (hH : ∀ p q, (K.d p (p + 1)).f q ≫ F (p + 1) q =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.d p (p + 1)).f q))
    (hV : ∀ p q, (K.X p).d q (q + 1) ≫ F p (q + 1) =
      F p q ≫ PositiveCohomologyConjugation.CM.Construction.restrictToRational.map ((L.X p).d q (q + 1))) :
    K.total (ComplexShape.up ℕ) ⟶ PositiveCohomologyConjugation.CM.Construction.restrictComplex (L.total (ComplexShape.up ℕ)) :=
  CochainComplex.ofHom (rationalComplexTotalDegreeMap K L F)
    (fun n => (rationalComplexTotalDegreeMap_comm K L F hH hV n).symm)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTotalMap.CM.Construction
