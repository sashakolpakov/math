import OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified.ZeroChartSheaf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.Seesaw
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseChanged

/-! # Relative Zero Triviality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified

noncomputable section

/-! Relative Picard zero of a fixed rigidified family gives an actual
global trivialization after every base change. The parameter family
is locally noetherian; its test scheme need not be. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {A B : Over (Spec (.of K))} [GrpObj A] [IsCommMonObj A]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  [IsLocallyNoetherian B.left] (D : ProductLine.Construction.RigidifiedProductLine A B)

theorem ProductLine.Construction.RigidifiedProductLine.class_trivial_of_relative_zero {T : Over (Spec (.of K))} (a : T ⟶ B)
    (h : D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  let π := (fst T A).left
  let M := D.line a
  have hn (x : T.left) : ∃ U : T.left.Opens, x ∈ U ∧ Nonempty
      ((Scheme.Modules.pullback (π ⁻¹ᵁ U).ι).obj M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (π ⁻¹ᵁ U).toScheme) := by
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (TopologicalSpace.Opens.mem_top (a.left x))
    let U := a.left ⁻¹ᵁ V
    let T' : Over (Spec (.of K)) := Over.mk (U.ι ≫ T.hom)
    let B' : Over (Spec (.of K)) := Over.mk (V.ι ≫ B.hom)
    let j : T' ⟶ T := Over.homMk U.ι rfl
    let b : B' ⟶ B := Over.homMk V.ι rfl
    let v : T' ⟶ B' := Over.homMk (a.left ∣_ V) (by
      change (a.left ∣_ V) ≫ (V.ι ≫ B.hom) = U.ι ≫ T.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, a.w])
    have hv : v ≫ b = j ≫ a := Over.OverMorphism.ext (morphismRestrict_ι a.left V)
    have : IsAffine B'.left := hV
    have : IsLocallyNoetherian B'.left := isLocallyNoetherian_of_isOpenImmersion V.ι
    have : IsNoetherianRing Γ(B'.left, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top B'.left⟩
    have hr : D.relativeValue (v ≫ b) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T' := by
      rw [hv, ← D.relativeValue_natural, h, AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass_naturality]
    have hc := (D.zeroChart_hasLift_iff_class b v).mp (D.zeroChart_hasLift_of_relative_zero b v hr)
    have hp : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (j ⊗ₘ 𝟙 A).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T' ⊗ A).left := by
      rw [D.line_class_pullback, ← hv]
      exact hc
    obtain ⟨e⟩ := Quotient.exact hp
    exact ⟨U, hxV, ⟨Quotients.FiniteDescent.BaseChanged.Construction.BaseChangedBundleFrames.openFrame (j ⊗ₘ 𝟙 A).left π U
      (fst T' A).left (Projective.ConstantFamily.Construction.tensorFamily_isPullback A T j) M.sheaf e⟩⟩
  let e : M.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ A).left :=
    Quotients.FiniteDescent.Seesaw.Construction.SeesawDescent.trivial π M.sheaf
      (Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.restricted_unit π
        (Quotients.FiniteDescent.CartesianProductIs.Construction.CartesianProductFunctions.isIso_app A.hom (snd T A).left π T.hom
          (IsPullback.of_hasPullback T.hom A.hom).flip)) hn
      (PolarizationKernel.Chart.Construction.polarizationFamilyAxis A) (PolarizationKernel.Chart.Construction.polarizationFamilyAxis_section A) (D.frame a)
  exact Quotient.sound ⟨e⟩

theorem ProductLine.Construction.RigidifiedProductLine.relative_zero_iff_class_trivial {T : Over (Spec (.of K))} (a : T ⟶ B) :
    D.relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T ↔
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (D.line a) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ A).left := by
  refine ⟨D.class_trivial_of_relative_zero a, fun h => ?_⟩
  unfold ProductLine.Construction.RigidifiedProductLine.relativeValue
  rw [h]
  rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Rigidified
