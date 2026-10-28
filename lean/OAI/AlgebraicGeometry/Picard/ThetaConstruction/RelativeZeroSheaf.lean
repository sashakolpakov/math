import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroCharts
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FamilyLiftFactorization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismSheafLifts
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Relative Zero Sheaf -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts

noncomputable section

/-! The varying-family zero chart classifies zero in the original
relative Picard sheaf. Its proved monomorphism glues local lifts for the
fppf topology without restricting test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S : Scheme} {A B : Over S} [GrpObj A]
    (D : AbelianScheme.IsogenyQuotient.Relative.RigidifiedLine.Construction.RelativeRigidifiedProductLine A B)

def zeroSubfunctor : Subfunctor (yoneda.obj B) where
  obj T := { a | D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T.unop }
  map j a ha := (D.relativeValue_natural j.unop a).symm.trans
    ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.map j) ha).trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j.unop))

theorem zeroSubfunctor_isSheaf :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (zeroSubfunctor D).toFunctor := by
  let J := Scheme.fppfTopology.over S
  have hB := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj B)
  apply ((zeroSubfunctor D).isSheaf_iff hB).mpr
  intro T a hR
  have hP : Presieve.IsSheaf J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj :=
    (isSheaf_iff_isSheaf_of_type J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).property
  apply (hP _ hR).isSeparatedFor.ext
  intro U j hj
  change D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U at hj
  exact (D.relativeValue_natural j a).trans (hj.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality A j).symm)

variable [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) {T : Over S}
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [IsLocallyNoetherian T.left]
    (a : T ⟶ B)

theorem zeroChart_hasLift_of_relative_zero {U : Over S} (j : U ⟶ T)
    (h : D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U) :
    Nonempty (Over.mk j.left ⟶ RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a) := by
  let J := Scheme.fppfTopology.over S
  let x : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a))
  let y : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left
  let : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)))
  let R : Sieve U := Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A) (X := op U) x y
  have hR : R ∈ J U := Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) x y h
  obtain ⟨v, hv⟩ := FormalGeometry.Completion.MonomorphismSheafLifts.Construction.mono_hasLift_of_coveringSieve J (FormalGeometry.Completion.FamilyLiftFactorization.Construction.compositeFamilyMap T (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a)) j R hR (by
    intro V z hz
    have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line ((z ≫ j) ≫ a)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (V ⊗ A).left := by
      change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line (j ≫ a))) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left) at hz
      rw [D.line_class_pullback, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial] at hz
      simpa only [Category.assoc] using hz
    obtain ⟨p⟩ := (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_hasLift_iff_class P D a (z ≫ j)).mpr hp
    let w := FormalGeometry.Completion.FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a) (z ≫ j) p
    exact ⟨w.val, w.property⟩)
  exact ⟨(FormalGeometry.Completion.FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a) j).symm ⟨v, hv⟩⟩

theorem zeroChart_hasLift_iff_relative_zero {U : Over S} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart P D a) ↔
      D.relativeValue (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U := by
  constructor
  · intro h
    have hc := (RelativeZeroCharts.Geometric.RelativeRigidifiedCharts.zeroChart_hasLift_iff_class P D a j).mp h
    exact congrArg (fun c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A).left =>
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op U) c) hc
  · exact zeroChart_hasLift_of_relative_zero D P a j

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeZeroSheaf.Geometric.RelativeRigidifiedCharts
