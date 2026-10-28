import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointBicharacter
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourcePolarizationAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PrescriptionActions

/-! # Reference Point Adjoints -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAdjoints.Construction

noncomputable section

/-! The original Rosati relation acts on every torsion-point bicharacter
through the actual integral coefficient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (n : ℕ) (hn : 0 < n)

theorem originalPointPairing_adjoint
    (p r : A.abelian.scheme ⟶ A.abelian.scheme) [IsMonHom p] [IsMonHom r]
    (h : CartierDuality.SheafBlocks.Construction.Schemes.ProjectorsAdjoint (CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme p)) n)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicMultiplicationSheafMaps.Construction.nativeAbelianEndomorphismGroup A.abelian.scheme r)) n))
    (T : Over (Spec (.of k))) (x y : (A.abelian.torsionFunctor n).obj (.op T)) :
    DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian A.abelian p n).app (.op T) x) y =
      DualityIntrinsicPointValues.Construction.originalPolarizationPairingValue A n hn T x ((PELModuli.CMPoints.DualityPairing.homOnTorsion A.abelian A.abelian r n).app (.op T) y) := by
  let G := CartierDuality.PolarizedTorsion.AbelianScheme.torsionSheaf (HomomorphismsPolarizationAdapter.Construction.e57AbelianOfBundled A.abelian) n
  let e := CartierDualityCanonical.Construction.e56SourceTorsionPairing A n hn
  let xp := Prescription.Construction.originalTorsionSheafPoint A.abelian n T x
  let yp := Prescription.Construction.originalTorsionSheafPoint A.abelian n T y
  have hx := PrescriptionActions.Construction.originalTorsionSheafPoint_endomorphism A.abelian n p T x
  have hy := PrescriptionActions.Construction.originalTorsionSheafPoint_endomorphism A.abelian n r T y
  exact (congrArg (fun z => (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) yp) z).down)
    hx.symm).trans ((congrArg ULift.down (h T xp yp)).trans
      (congrArg (fun z => (CartierDuality.SheafEvaluation.Construction.Schemes.sheafCharacterValue G T (e.rightAdjoint.hom.app (.op T) z) xp).down) hy))

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation A ρ)

abbrev originalPointPairing_coefficient_adjoint (a : NumberField.RingOfIntegers E) :=
  originalPointPairing_adjoint A n hn (ρ.map a)
    (ρ.map (NumberField.IsCMField.ringOfIntegersComplexConj E a))
    (SourcePolarizationAdjoints.Construction.sourceCanonicalPairing_coefficient_adjoint A ρ hρ n hn a)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ReferencePointAdjoints.Construction
