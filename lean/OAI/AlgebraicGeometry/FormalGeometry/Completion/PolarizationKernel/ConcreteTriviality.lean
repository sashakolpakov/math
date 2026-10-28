import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.KernelSheaf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Seesaw
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseChanged

/-! # Concrete Triviality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ConcreteTriviality

noncomputable section

/-! Vanishing of the actual relative Picard section gives an actual
global trivialization of the axis-rigidified polarization family.
Local frames descend by the counit; constancy of functions is derived. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ A)

theorem polarizationFamilyClass_zero_of_relative_zero_affine
    [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)]
    (h : Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Polarization.Family.Construction.polarizationFamilyClass A L a = 0 := by
  have h' : Polarization.PicardMap.Construction.polarizationRelativeSection A L (𝟙 T ≫ a) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T := by simpa using h
  have hz := (Chart.Construction.polarizationKernelChart_hasLift_iff A L a (𝟙 T)).mp
    (KernelSheaf.Construction.polarizationKernelChart_hasLift_of_relative_zero A L a (𝟙 T) h')
  simpa using hz

theorem polarizationFamilyClass_zero_of_relative_zero [IsLocallyNoetherian T.left]
    (h : Polarization.PicardMap.Construction.polarizationRelativeSection A L a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Polarization.Family.Construction.polarizationFamilyClass A L a = 0 := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let π := (fst T A).left
  let M := Polarization.FamilyBundle.Construction.polarizationFamilyBundle A L a
  have hn (x : T.left) : ∃ U : T.left.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ U).toScheme) := by
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    let T' : Over (Spec (CommRingCat.of K)) := Over.mk (U.ι ≫ T.hom)
    let j : T' ⟶ T := Over.homMk U.ι rfl
    have : IsAffine T'.left := hU
    have : IsLocallyNoetherian T'.left := isLocallyNoetherian_of_isOpenImmersion U.ι
    have : IsNoetherianRing Γ(T'.left, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T'.left⟩
    have hz : Polarization.Family.Construction.polarizationFamilyClass A L (j ≫ a) = 0 :=
      polarizationFamilyClass_zero_of_relative_zero_affine A L (j ≫ a) (by
        rw [← Polarization.PicardMap.Construction.polarizationRelativeSection_natural, h, AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality])
    have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T' ⊗ A).left := by
      rw [Polarization.FamilyBundle.Construction.polarizationFamilyBundle_pullback, hz]
      rfl
    obtain ⟨e⟩ := Quotient.exact hc
    exact ⟨U, hxU, ⟨Quotients.FiniteDescent.BaseChanged.Construction.BaseChangedBundleFrames.openFrame (j ⊗ₘ 𝟙 A).left π U
      (fst T' A).left (Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j) M.sheaf e⟩⟩
  let e : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ A).left :=
    Quotients.FiniteDescent.Seesaw.Construction.SeesawDescent.trivial π M.sheaf
      (Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.restricted_unit π
        (Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.isIso_app A.hom (snd T A).left π T.hom
          (IsPullback.of_hasPullback T.hom A.hom).flip)) hn
      (Chart.Construction.polarizationFamilyAxis A) (Chart.Construction.polarizationFamilyAxis_section A) (Polarization.FamilyBundle.Construction.polarizationFamilyRigidification A L a)
  apply Additive.toMul.injective
  exact (Polarization.FamilyBundle.Construction.polarizationFamilyBundle_class A L a).symm.trans (Quotient.sound ⟨e⟩)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolarizationKernel.ConcreteTriviality
