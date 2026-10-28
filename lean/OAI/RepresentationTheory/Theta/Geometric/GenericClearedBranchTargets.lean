import OAI.RepresentationTheory.Theta.Geometric.Reference.GenericPELFamily
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.BranchLattices

/-! # Generic Cleared Branch Targets -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual generic correspondence endpoints give the literal complex
cleared branch targets after undoing the same actual marking shift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.complexGenericPointEquiv_iterate (σ : D.pel.space ≅ D.pel.space)
    (n : ℕ) (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace) :
    Data.ActiveHeckeThetaData.complexGenericPointEquiv
      ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map σ.hom))^[n] y) =
      (fun z => z ≫ σ.hom)^[n] (Data.ActiveHeckeThetaData.complexGenericPointEquiv y) := by
  have h : Function.Semiconj (Data.ActiveHeckeThetaData.complexGenericPointEquiv (D := D))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map σ.hom))
      (fun z => z ≫ σ.hom) :=
    fun z => AlgebraicGeometry.AbelianScheme.TateComparison.CorrespondencePointBaseChange.pointBaseChangeEquiv_comp D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) σ.hom z
  exact h.iterate_right n y

theorem Data.ActiveHeckeThetaData.exists_clearedBranch_of_generic_endpoint
    (hg : D.pel.HasIntegralModelGeometry) {c : D.domain → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace}
    (hc : Continuous c) (σ : D.pel.space ≅ D.pel.space) (a : Intrinsic.Hecke.ActiveWeight)
    (x : D.domain) (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints D.pel.complexSpace)
    (hp : ∃ p : (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).Fiber
      (D.branchGenericPoint c x),
      p.val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
        (fun z => z ≫ σ.hom)^[Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a]
          (Data.ActiveHeckeThetaData.complexGenericPointEquiv y)) :
    ∃ b : D.ClearedBranch c a, D.clearedBranchTarget σ b x = y := by
  obtain ⟨p, hp⟩ := hp
  let β := D.nativeClearedBranchGenericFiberEquiv hg hc a x
  let b := β.symm p
  have hb : β b = p := β.apply_symm_apply p
  have he := (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).baseChangeFiberEquiv_endpoint
    D.pel.complexGenericPoint (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (c x)
    (D.nativeClearedBranchFiberEquiv hg hc a x b)
  change Data.ActiveHeckeThetaData.complexGenericPointEquiv
    (b.lift x ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target) =
      (β b).val ≫ (D.pel.correspondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target at he
  rw [hb, hp] at he
  have ht : b.lift x ≫ (D.pel.complexCorrespondence (Intrinsic.Hecke.clearedActiveType D.pel.reference.distinguished a)).target =
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map σ.hom))^[
        Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a] y := by
    apply (Data.ActiveHeckeThetaData.complexGenericPointEquiv (D := D)).injective
    exact he.trans (D.complexGenericPointEquiv_iterate σ _ y).symm
  refine ⟨b, ?_⟩
  rw [Data.ActiveHeckeThetaData.clearedBranchTarget, ht]
  have hi : Function.LeftInverse
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map σ.inv))
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map ((Over.pullback D.pel.complexGenericPoint).map σ.hom)) := by
    intro z
    change (z ≫ (Over.pullback D.pel.complexGenericPoint).map σ.hom) ≫
      (Over.pullback D.pel.complexGenericPoint).map σ.inv = z
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  exact hi.iterate _ y

end

end OAI.RepresentationTheory.Theta.Geometric
