import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalFiltrationQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.TensorSingle
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-! # Brutal Tensor Spectral Sequence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalTensorSpectralSequence

noncomputable section

/-! A spectral sequence for the tensor of two actual cochain complexes.
The first page is identified with the homology of the individual columns.
The library numbers this initial page `2`. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R] (A K : CochainComplex (ModuleCat.{0} R) ℤ)

def spectralSequence : E₂CohomologicalSpectralSequence (ModuleCat.{0} R) :=
  Tensor.SpectralObject.spectralSequence R K (BrutalFiltration.filtration R A)

def firstPageXIso (p q : ℤ) :
    ((spectralSequence R A K).page 2).X (p, q) ≅
      ((Tensor.Homotopy.complexFunctor R K).obj
        (BrutalFiltrationQuotient.quotient R A q)).homology (p + q) :=
  (Tensor.SpectralObject.abelian R K (BrutalFiltration.filtration R A)).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological (p, q)
    (q : EInt) ((q + 1 : ℤ) : EInt) rfl rfl (p + q) rfl ≪≫
    BrutalFiltrationQuotient.relativeTermIso R A q K (p + q)

def firstPageFlatIso (p q : ℤ) [Module.Flat R (A.X (-(q + 1)))] :
    ((spectralSequence R A K).page 2).X (p, q) ≅
      (tensorLeft (A.X (-(q + 1)))).obj (K.homology (p + 2 * q + 1)) :=
  firstPageXIso R A K p q ≪≫
    Tensor.TensorSingle.flatHomologyIso R (A.X (-(q + 1))) K (-(q + 1)) (p + q) ≪≫
    (tensorLeft (A.X (-(q + 1)))).mapIso (eqToIso (by congr 1; omega))

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BrutalTensorSpectralSequence
