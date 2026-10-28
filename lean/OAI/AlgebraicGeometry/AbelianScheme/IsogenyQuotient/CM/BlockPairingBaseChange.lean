import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.BlockPairingValues
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsPerfectKernel

/-! # Block Pairing Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.BlockPairingBaseChange.Construction

noncomputable section

/-! The CMPoints chosen/opposite pairings after actual source base change
are the pullbacks of the original literal block restrictions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E L : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S T : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ)) (f : T ⟶ S)
  (b : Annihilator.Construction.SchemeBicharacter (A := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h))
    (B := Torsion.Groups.Construction.nativeTorsionScheme A.scheme (q ^ h)) (W := (CartierDuality.CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X))

set_option backward.isDefEq.respectTransparency false in
theorem l45SourceBlockPairing_baseChange (i : Fin s) :
    PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit (A.pullback f) (σ.pullback f) h s labels
      (Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback f (Grp.mk A.scheme) (Grp.mk A.scheme) (q ^ h) b) i =
    Intrinsic.BlockPairingBaseChange.Construction.nativeBlockPairingPullback A
      (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i)
      (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels i) (q ^ h) f
      (PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit A σ h s labels b i) :=
  Intrinsic.BlockPairingValues.Construction.nativeBlockPairingPullback_source_restriction A
    (PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i)
    (PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels i) (q ^ h) f b

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.BlockPairingBaseChange.Construction
