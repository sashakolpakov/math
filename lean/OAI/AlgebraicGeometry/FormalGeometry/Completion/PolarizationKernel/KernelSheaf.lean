import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.Chart
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.PicardMap
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FamilyLiftFactorization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismSheafLifts
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Kernel Sheaf -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.KernelSheaf

noncomputable section

/-! The derived kernel chart represents the kernel of the actual fppf
Picard map. Local trivializations descend through the chart's proved
monomorphism; no represented dual or Picard descent data are assumed. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))}
  [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] (a : T ⟶ A)

theorem polarizationKernelChart_hasLift_of_relative_zero
    {U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T)
    (h : Polarization.PicardMap.Construction.polarizationRelativeSection A L (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U) :
    Nonempty (Over.mk j.left ⟶ Chart.Construction.polarizationKernelChart A L a) := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  let x : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := (Polarization.Family.Construction.polarizationFamilyClass A L (j ≫ a)).toMul
  let y : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).obj (op U) := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left
  have : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)))
  let R : Sieve U := Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A) (X := op U) x y
  have hR : R ∈ J U := Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) x y h
  obtain ⟨v, hv⟩ := MonomorphismSheafLifts.Construction.mono_hasLift_of_coveringSieve J
    (FamilyLiftFactorization.Construction.compositeFamilyMap T (Chart.Construction.polarizationKernelChart A L a)) j R hR (by
      intro V z hz
      have hp : Polarization.Family.Construction.polarizationFamilyClass A L (z ≫ (j ≫ a)) = 0 := by
        apply Additive.toMul.injective
        have hn := congrArg Additive.toMul (Polarization.Family.Construction.polarizationFamilyClass_pullback A L z (j ≫ a))
        change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (Polarization.Family.Construction.polarizationFamilyClass A L (j ≫ a)).toMul =
          AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (z ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left) at hz
        exact hn.symm.trans (hz.trans (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (z ⊗ₘ 𝟙 A).left))
      have hp' : Polarization.Family.Construction.polarizationFamilyClass A L ((z ≫ j) ≫ a) = 0 := by
        simpa only [Category.assoc] using hp
      obtain ⟨p⟩ := (Chart.Construction.polarizationKernelChart_hasLift_iff A L a (z ≫ j)).mpr hp'
      let w := FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (Chart.Construction.polarizationKernelChart A L a) (z ≫ j) p
      exact ⟨w.val, w.property⟩)
  exact ⟨(FamilyLiftFactorization.Construction.familyLiftFactorizationEquiv T (Chart.Construction.polarizationKernelChart A L a) j).symm ⟨v, hv⟩⟩

theorem polarizationKernelChart_hasLift_iff_relative_zero
    {U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) :
    Nonempty (Over.mk j.left ⟶ Chart.Construction.polarizationKernelChart A L a) ↔
      Polarization.PicardMap.Construction.polarizationRelativeSection A L (j ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A U := by
  constructor
  · intro h
    have hz := (Chart.Construction.polarizationKernelChart_hasLift_iff A L a j).mp h
    unfold Polarization.PicardMap.Construction.polarizationRelativeSection
    rw [hz]
    rfl
  · exact polarizationKernelChart_hasLift_of_relative_zero A L a j

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.KernelSheaf
