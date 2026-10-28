import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.KernelSheaf

/-! # Triviality Sieve -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.TrivialitySieve

noncomputable section

/-! Vanishing in the actual Picard sheaf is equivalent to local
vanishing of the actual polarization line class. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A)

def polarizationTrivialitySieve : Sieve T :=
  Presheaf.equalizerSieve (F := AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A) (X := op T)
    (Family.Construction.polarizationFamilyClass A L a).toMul (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left)

theorem polarizationTrivialitySieve_apply {U : Over (Spec (CommRingCat.of K))} (j : U ⟶ T) :
    polarizationTrivialitySieve A L a j ↔ Family.Construction.polarizationFamilyClass A L (j ≫ a) = 0 := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (Family.Construction.polarizationFamilyClass A L a).toMul =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left) ↔ _
  rw [AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  have hn := congrArg Additive.toMul (Family.Construction.polarizationFamilyClass_pullback A L j a)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (Family.Construction.polarizationFamilyClass A L a).toMul =
    (Family.Construction.polarizationFamilyClass A L (j ≫ a)).toMul at hn
  rw [hn]
  exact ⟨fun h => Additive.toMul.injective h, fun h => congrArg Additive.toMul h⟩

theorem polarizationTrivialitySieve_mem_iff :
    polarizationTrivialitySieve A L a ∈ (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) T ↔
      PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by
  let J := Scheme.fppfTopology.over (Spec (CommRingCat.of K))
  constructor
  · intro hR
    have hP : Presieve.IsSheaf J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj :=
      (isSheaf_iff_isSheaf_of_type J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj).mp (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).property
    apply (hP _ hR).isSeparatedFor.ext
    intro U j hj
    rw [PicardMap.Construction.polarizationRelativeSection_natural, AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality]
    have hz := (polarizationTrivialitySieve_apply A L a j).mp hj
    unfold PicardMap.Construction.polarizationRelativeSection
    rw [hz]
    rfl
  · intro h
    have : Presheaf.IsLocallyInjective J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A) :=
      inferInstanceAs (Presheaf.IsLocallyInjective J (toSheafify J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A)))
    exact Presheaf.equalizerSieve_mem J (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A)
      (Family.Construction.polarizationFamilyClass A L a).toMul (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left) h

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Polarization.TrivialitySieve
