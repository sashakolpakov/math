import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SectionBicharacter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.DualityIntrinsicPointValues
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Prescription

/-! # Reference Point Bicharacter -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointBicharacter.Construction

noncomputable section

/-! The original canonical torsion values form a bicharacter on the
actual HilbertConstruction torsion points, including nonreduced test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

instance originalTorsionPoint_commGroup {S : Scheme} {d : ℕ}
    (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) (m : ℕ) (U : Over S) :
    CommGroup ((B.torsionFunctor m).obj (.op U)) :=
  inferInstanceAs (CommGroup (B.torsionPoints m U))

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of k)))

def originalPointBicharacter :
    (A.abelian.torsionFunctor n).obj (.op T) →*
      (A.abelian.torsionFunctor n).obj (.op T) →*
        (T ⟶ (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec (.of k))).X) :=
  (((SectionBicharacter.Construction.sheafSectionBicharacter (CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn) T).comp
    (Prescription.Construction.originalTorsionSheafPointMulEquiv A.abelian n T).toMonoidHom).compl₂
      (Prescription.Construction.originalTorsionSheafPointMulEquiv A.abelian n T).toMonoidHom).compr₂
        MulEquiv.ulift.toMonoidHom

theorem originalPointBicharacter_value
    (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    originalPointBicharacter A n hn T x y = DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T x y :=
  congrArg ULift.down (SectionBicharacter.Construction.sheafSectionBicharacter_right (CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn) T
    (Prescription.Construction.originalTorsionSheafPoint A.abelian n T x) (Prescription.Construction.originalTorsionSheafPoint A.abelian n T y))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointBicharacter.Construction
