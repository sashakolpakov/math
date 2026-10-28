import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.ColumnHomology
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalSpectralDifferential
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalConnectingModuleMap

/-! # Second Page -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SecondPage

noncomputable section

/-! The next page of the native tensor spectral sequence is computed from
the original complex tensored with the homology of the other complex.
The library numbers the initial page `2` and this next page `3`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)
  [∀ i, Module.Flat R (A.X i)]

def firstPageIso (p q k : ℤ) (h : p + 2 * q + 1 = k) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 2).X (p, q) ≅
      (tensorRight (K.homology k)).obj (A.X (-(q + 1))) :=
  BrutalTensorSpectralSequence.firstPageXIso R A K p q ≪≫
    ColumnHomology.iso R K (A.X (-(q + 1))) (-(q + 1)) (p + q) k (by omega)

@[reassoc]
theorem firstPage_d (p q k : ℤ) (h : (p + 2) + 2 * q + 1 = k) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 2).d (p, q + 1) (p + 2, q) ≫
      (firstPageIso R A K (p + 2) q k h).hom =
    (firstPageIso R A K p (q + 1) k (by omega)).hom ≫
      (tensorRight (K.homology k)).map (A.d (-((q + 1) + 1)) (-(q + 1))) := by
  simp only [firstPageIso, Iso.trans_hom]
  rw [← Category.assoc, BrutalSpectralDifferential.firstPage_d]
  simp only [Category.assoc]
  congr 1
  exact ColumnHomology.shifted_naturality R K
    1 (-((q + 1) + 1)) (-(q + 1)) (p + (q + 1)) ((p + 2) + q) k (by omega) (by omega) (by omega)
    (BrutalConnectingMap.columnConnecting R A q) (A.d (-((q + 1) + 1)) (-(q + 1)))
    (BrutalConnectingModuleMap.eq_module_map R A q)

def shortComplexIso (p q k : ℤ) (h : (p + 2) + 2 * (q + 1) + 1 = k) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 2).sc'
      (p, (q + 1) + 1) (p + 2, q + 1) ((p + 2) + 2, q) ≅
    (((tensorRight (K.homology k)).mapHomologicalComplex (.up ℤ)).obj A).sc'
      (-(((q + 1) + 1) + 1)) (-((q + 1) + 1)) (-(q + 1)) :=
  ShortComplex.isoMk
    (firstPageIso R A K p ((q + 1) + 1) k (by omega))
    (firstPageIso R A K (p + 2) (q + 1) k h)
    (firstPageIso R A K ((p + 2) + 2) q k (by omega))
    (firstPage_d R A K p (q + 1) k h).symm
    (firstPage_d R A K (p + 2) q k (by omega)).symm

def iso (p q k : ℤ) (h : (p + 2) + 2 * (q + 1) + 1 = k) :
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 3).X (p + 2, q + 1) ≅
      (((tensorRight (K.homology k)).mapHomologicalComplex (.up ℤ)).obj A).homology (-((q + 1) + 1)) :=
  ((BrutalTensorSpectralSequence.spectralSequence R A K).iso 2 3 (p + 2, q + 1)).symm ≪≫
    ((BrutalTensorSpectralSequence.spectralSequence R A K).page 2).homologyIsoSc'
      (p, (q + 1) + 1) (p + 2, q + 1) ((p + 2) + 2, q)
      (by
        apply ComplexShape.prev_eq'
        change (p + 2, ((q + 1) + 1) + (1 - 2)) = (p + 2, q + 1)
        congr 1
        omega)
      (by
        apply ComplexShape.next_eq'
        change ((p + 2) + 2, (q + 1) + (1 - 2)) = ((p + 2) + 2, q)
        congr 1
        omega) ≪≫
    ShortComplex.homologyMapIso (shortComplexIso R A K p q k h) ≪≫
    ((((tensorRight (K.homology k)).mapHomologicalComplex (.up ℤ)).obj A).homologyIsoSc'
      (-(((q + 1) + 1) + 1)) (-((q + 1) + 1)) (-(q + 1))
      (by apply ComplexShape.prev_eq'; change -(((q + 1) + 1) + 1) + 1 = -((q + 1) + 1); omega)
      (by apply ComplexShape.next_eq'; change -((q + 1) + 1) + 1 = -(q + 1); omega)).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SecondPage
