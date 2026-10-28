import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectiveOpen
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveBaseChange

/-! # Balanced Affine Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedAffineCover

noncomputable section

/-! Explicit affine charts cover the stable projective open. Its
quasi-projective presentation persists after arbitrary scheme base change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ} (i : Fin m)

def stableBalancedAffineChartMap (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    Spec (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced)) ⟶
      (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := r) i).left :=
  (BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).inv ≫
    (Proj (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)).homOfLE (le_iSup (BalancedProjectiveOpen.stableBalancedFrameOpen R i) j)

instance stableBalancedAffineChartMap_open (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    IsOpenImmersion (stableBalancedAffineChartMap R i j) := by
  exact IsOpenImmersion.comp (BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).inv
    ((Proj (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)).homOfLE (le_iSup (BalancedProjectiveOpen.stableBalancedFrameOpen R i) j))

theorem stableBalancedAffineChartMap_comp_inclusion (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} r m) :
    stableBalancedAffineChartMap R i j ≫ (BalancedProjectiveOpen.stableBalancedProjectiveOpen R (r := r) i).ι =
      Proj.awayι (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)
        (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R j.exponent j.balanced)
        (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R j.exponent j.balanced i)
        (j.degree_positive i) := by
  unfold stableBalancedAffineChartMap
  erw [Category.assoc, Scheme.homOfLE_ι]; rfl

def stableBalancedAffineOpenCover : (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := r) i).left.OpenCover where
  I₀ := BalancedFrameIndex.StableBalancedFrameIndex.{u} r m
  X j := Spec (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))
  f j := stableBalancedAffineChartMap R i j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    let y : (BalancedProjectiveOpen.stableBalancedFrameOpen R i j).toScheme := ⟨x.val, hj⟩
    refine ⟨j, (BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).hom y, ?_⟩
    apply Subtype.ext
    change ((Proj (Balanced.DeterminantGrading.balancedDeterminantGrading R r m i)).homOfLE
      (le_iSup (BalancedProjectiveOpen.stableBalancedFrameOpen R i) j)
      ((BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).inv ((BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).hom y))).val = _
    exact (Scheme.homOfLE_apply (le_iSup (BalancedProjectiveOpen.stableBalancedFrameOpen R i) j)
      ((BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).inv ((BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).hom y))).trans
      (congrArg (fun f : (BalancedProjectiveOpen.stableBalancedFrameOpen R i j).toScheme ⟶
        (BalancedProjectiveOpen.stableBalancedFrameOpen R i j).toScheme => (f y).val)
        (BalancedProjectiveOpen.stableBalancedFrameOpenIsoSpec R i j).hom_inv_id)

theorem stableBalancedQuotientScheme_baseChange_quasiProjective
    [IsNoetherianRing R] (hr : 0 < r) (S : Scheme.{u}) (f : S ⟶ Spec (.of R)) :
    Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation ((Over.pullback f).obj (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := r) i))) := by
  obtain ⟨P⟩ := BalancedProjectiveOpen.stableBalancedQuotientScheme_quasiProjective R i hr
  exact ⟨P.baseChange f⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedAffineCover
