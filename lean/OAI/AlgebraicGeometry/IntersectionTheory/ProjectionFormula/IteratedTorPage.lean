import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.SecondPage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CochainTor
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-! # Iterated Tor Page -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorPage

noncomputable section

/-! The third numbered page of the native tensor spectral sequence is
the iterated Tor module for actual projective resolutions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

variable (R : Type) [CommRing R]

theorem flat_cochain_terms (M : ModuleCat.{0} R) (P : ProjectiveResolution M) (i : ℤ) :
    Module.Flat R ((ChainToCochain.cochain R P.complex).X i) := by
  by_cases hi : 0 < i
  · let := ModuleCat.subsingleton_of_isZero (ChainToCochain.positive_zero R P.complex i hi)
    infer_instance
  · have he : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    rw [← he]
    exact Module.Flat.of_linearEquiv (ChainToCochain.termIso R P.complex (-i).toNat).toLinearEquiv

def rightTorIso (M N : ModuleCat.{0} R) (P : ProjectiveResolution N) (i : ℕ) :
    (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj
      (ChainToCochain.cochain R P.complex)).homology (-(i : ℤ)) ≅
      ((Tor (ModuleCat.{0} R) i).obj M).obj N :=
  HomologicalComplex.homologyMapIso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight M).symm (.up ℤ)).app
      (ChainToCochain.cochain R P.complex)) (-(i : ℤ)) ≪≫
    CochainTor.iso R M N P i

def spectralSequence (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L) :
    E₂CohomologicalSpectralSequence (ModuleCat.{0} R) :=
  BrutalTensorSpectralSequence.spectralSequence R (ChainToCochain.cochain R Q.complex)
    (((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R P.complex))

def iso (L M N : ModuleCat.{0} R) (P : ProjectiveResolution M) (Q : ProjectiveResolution L) (i j : ℕ) :
    ((spectralSequence R L M N P Q).page 3).X (1 - 2 * (i : ℤ) - (j : ℤ), (i : ℤ) - 1) ≅
      ((Tor (ModuleCat.{0} R) i).obj (((Tor (ModuleCat.{0} R) j).obj N).obj M)).obj L := by
  let A := ChainToCochain.cochain R Q.complex
  let K := ((tensorLeft N).mapHomologicalComplex (.up ℤ)).obj (ChainToCochain.cochain R P.complex)
  let : ∀ n, Module.Flat R (A.X n) := flat_cochain_terms R L Q
  have e : ((spectralSequence R L M N P Q).page 3).X (1 - 2 * (i : ℤ) - (j : ℤ), (i : ℤ) - 1) ≅
      (((tensorRight (K.homology (-(j : ℤ)))).mapHomologicalComplex (.up ℤ)).obj A).homology (-(i : ℤ)) := by
    convert Tensor.SecondPage.iso R A K (-(j : ℤ) - 2 * (i : ℤ) - 1) ((i : ℤ) - 2) (-(j : ℤ)) (by omega)
      using 2 <;> congr 1 <;> omega
  exact e ≪≫ rightTorIso R (K.homology (-(j : ℤ))) L Q i ≪≫
    ((Tor (ModuleCat.{0} R) i).mapIso (CochainTor.iso R N M P j)).app L

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IteratedTorPage
