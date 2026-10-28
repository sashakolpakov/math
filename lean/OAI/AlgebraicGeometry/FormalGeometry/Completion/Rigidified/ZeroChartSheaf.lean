import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ProductZeroChart
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FamilyLiftFactorization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismSheafLifts
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Zero Chart Sheaf -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! The normalized-frame chart represents the zero fiber in the
actual relative Picard sheaf. Local lifts descend through its proved
monomorphism, including on nonreduced test schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (D : ProductLine.Construction.RigidifiedProductLine A B) {T : Over (Spec (.of K))}
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ B)

theorem ProductLine.Construction.RigidifiedProductLine.zeroChart_hasLift_of_relative_zero {U : Over (Spec (.of K))} (j : U ⟶ T)
    (h : D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U) :
    Nonempty (Over.mk j.left ⟶ D.zeroChart a) := by
  let J := Scheme.fppfTopology.over (Spec (.of K))
  let x : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a))
  let y : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left
  have : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)))
  let R : Sieve U := Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A) (X := op U) x y
  have hR : R ∈ J U := Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) x y h
  obtain ⟨v, hv⟩ := MonomorphismSheafLifts.Construction.mono_hasLift_of_coveringSieve J (FamilyLiftFactorization.Construction.compositeFamilyMap T (D.zeroChart a)) j R hR (by
    intro V z hz
    have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line ((z ≫ j) ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (V ⊗ A).left := by
      change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left) at hz
      rw [D.line_class_pullback, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial] at hz
      simpa only [Category.assoc] using hz
    obtain ⟨p⟩ := (D.zeroChart_hasLift_iff_class a (z ≫ j)).mpr hp
    let w := FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (D.zeroChart a) (z ≫ j) p
    exact ⟨w.val, w.property⟩)
  exact ⟨(FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (D.zeroChart a) j).symm ⟨v, hv⟩⟩

theorem ProductLine.Construction.RigidifiedProductLine.zeroChart_hasLift_iff_relative_zero {U : Over (Spec (.of K))} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ D.zeroChart a) ↔ D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U := by
  constructor
  · intro h
    have hc := (D.zeroChart_hasLift_iff_class a j).mp h
    unfold ProductLine.Construction.RigidifiedProductLine.relativeValue
    rw [hc]
    rfl
  · exact D.zeroChart_hasLift_of_relative_zero a j

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
