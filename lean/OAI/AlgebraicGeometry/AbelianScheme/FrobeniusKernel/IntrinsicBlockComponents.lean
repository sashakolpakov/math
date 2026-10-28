import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CanonicalBlockComponents

/-! # Intrinsic Block Components -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockComponents.Construction

noncomputable section

/-! The original coefficient components are represented by actual
points of the corresponding native block, naturally on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (n : ℕ) (τ : Gal(E/ℚ))

def nativeBlockComponent (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    T ⟶ (CMPointsAt.Construction.l45ChosenBlock j iota hsplit A ρ τ n).X :=
  (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).inv.app (.op T)
    ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A.abelian ρ n τ).app (.op T) y)

theorem nativeBlockComponent_value (T : Over (Spec (.of k)))
    (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint j iota hsplit A ρ n τ T
      (nativeBlockComponent j iota hsplit A ρ n τ T y) =
        Prescription.Construction.prescribedBlockComponent j iota hsplit A ρ n τ T y := by
  let e := ((CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A.abelian ρ n τ).app (.op T)).groupIsoToMulEquiv
  exact congrArg ((PELModuli.CMPoints.BlocksProjectors.blockInclusion A.abelian ρ (j.localCharacter iota τ) n).app (.op T))
    (e.apply_symm_apply ((PELModuli.CMPoints.BlockRetraction.torsionProjectionNat j iota hsplit A.abelian ρ n τ).app (.op T) y))

theorem nativeBlockComponent_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (y : (A.abelian.torsionFunctor (q ^ n)).obj (.op T)) :
    t ≫ nativeBlockComponent j iota hsplit A ρ n τ T y =
      nativeBlockComponent j iota hsplit A ρ n τ U ((A.abelian.torsionFunctor (q ^ n)).map t.op y) := by
  apply CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_injective j iota hsplit A ρ n τ U
  exact (CanonicalBlockComponents.Construction.canonicalOriginalBlockPoint_natural j iota hsplit A ρ n τ t
    (nativeBlockComponent j iota hsplit A ρ n τ T y)).trans
      ((congrArg ((A.abelian.torsionFunctor (q ^ n)).map t.op)
        (nativeBlockComponent_value j iota hsplit A ρ n τ T y)).trans
          ((CanonicalBlockComponents.Construction.prescribedBlockComponent_natural j iota hsplit A ρ n τ t y).trans
            (nativeBlockComponent_value j iota hsplit A ρ n τ U
              ((A.abelian.torsionFunctor (q ^ n)).map t.op y)).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockComponents.Construction
