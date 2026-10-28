import OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology
import OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary
import OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

/-! # Compact Definite Place -/

namespace OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace

noncomputable section

/-! Every definite native archimedean special-unitary factor is compact,
using exactly the specified field coordinates and orthonormal basis. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.UnitaryCoordinateTopology OAI.RepresentationTheory.Theta.Adelic.CompactStandardUnitary

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def nativeNormalizedUnitary (v : Fin A.places) :
    SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v))) ≃ₜ*
      SpecialUnitary.SU (Matrix.diagonal (fun i : Fin 3 => if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1)) :=
  (UnitaryCoordinateTopology.specialUnitaryFieldContinuousEquiv (A.complex v) (A.complex_star v)
    (A.complex_continuous v) (A.complex_inverse_continuous v)
    (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))).trans
      (UnitaryCoordinateTopology.specialUnitaryBasisContinuousEquiv _ _ (A.basisV v) (A.formV v))

theorem native_definite_compact (v : Fin A.places) (hv : v ≠ A.distinguished) :
    CompactSpace (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))) := by
  have hM : Matrix.diagonal (fun i : Fin 3 =>
      if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1) = 1 := by simp [hv]
  let : CompactSpace (SpecialUnitary.SU (Matrix.diagonal (fun i : Fin 3 =>
      if v = A.distinguished ∧ i = 2 then (-1 : ℂ) else 1))) :=
    hM.symm ▸ CompactStandardUnitary.standardUnitary_compact
  exact (nativeNormalizedUnitary A v).symm.toHomeomorph.compactSpace

end

end OAI.RepresentationTheory.Theta.Adelic.CompactDefinitePlace
