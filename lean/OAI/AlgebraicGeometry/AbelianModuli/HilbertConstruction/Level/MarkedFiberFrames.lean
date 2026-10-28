import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FamilyEvaluationMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LineBundleCommonFrames

/-! # Marked Fiber Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The finitely many line bundles obtained by restricting the uniform
graph power to all marked torsion sections can be trivialized together
on affine neighborhoods. Their transported frames are frames of the
actual marked fibers in the restricted polarized family. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (level : A.abelian.FullLevel n)

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_markedFiberFrames_affineOpen (z : S) :
    ∃ U : S.Opens, z ∈ U ∧ IsAffineOpen U ∧
      ∀ i : Fin (n ^ (2 * g)), Nonempty
        (((A.pullback U.ι).uniformFrameLineBundle.pullback
          ((A.pullback U.ι).fullLevelSectionAtIndex (level.pullback U.ι) i)).sheaf ≅
            Line.Bundles.structureModule U.toScheme) := by
  let L := A.uniformFrameLineBundle
  let x := A.fullLevelSectionAtIndex level
  let ls := List.ofFn (fun i : Fin (n ^ (2 * g)) => L.pullback (x i))
  obtain ⟨U, hz, hU, hframes⟩ := Finite.LineBundleCommonFrames.finiteLineBundles_common_affine_frame ls z
  refine ⟨U, hz, hU, fun i => ?_⟩
  let B := A.pullback U.ι
  let π := pullback.fst A.abelian.scheme.hom U.ι
  let y := B.fullLevelSectionAtIndex (level.pullback U.ι) i
  have hy : y ≫ π = U.ι ≫ x i :=
    A.abelian.fullLevelGlobalSection_pullback level U.ι (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i)
  let d := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  let H : (L.pullback π).sheaf ≅ B.uniformFrameLineBundle.sheaf :=
    A.graphBundle.powerBaseChangeIso π d ≪≫
      (TensorPower.Maps.tensorPowerFunctor B.abelian.scheme.left d).mapIso (A.graphBundle_baseChangeIso U.ι).symm
  obtain ⟨f⟩ := hframes (L.pullback (x i)) (by
    simp only [ls, List.mem_ofFn]
    exact ⟨i, rfl⟩)
  exact ⟨(Scheme.Modules.pullback y).mapIso H.symm ≪≫
    Family.FramedEvaluationBaseChange.familySectionFiberComparison L U.ι π (x i) y hy ≪≫ f⟩

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_markedFiberFrames_affineOpenCover :
    ∃ C : Scheme.OpenCover.{u} S, (∀ i, IsAffine (C.X i)) ∧
      ∀ i, ∀ j : Fin (n ^ (2 * g)), Nonempty
        (((A.pullback (C.f i)).uniformFrameLineBundle.pullback
          ((A.pullback (C.f i)).fullLevelSectionAtIndex (level.pullback (C.f i)) j)).sheaf ≅
            Line.Bundles.structureModule (C.X i)) := by
  choose U hz hU he using A.exists_markedFiberFrames_affineOpen level
  let C : Scheme.OpenCover.{u} S := {
    I₀ := S
    X z := (U z).toScheme
    f z := (U z).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun z => ⟨z, ⟨⟨z, hz z⟩, rfl⟩⟩, inferInstance⟩ }
  exact ⟨C, hU, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
