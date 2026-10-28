import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CechSheafPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructurePullbackLinear
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechPullbackData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.Add
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

/-! # Structure Cech Refined Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechRefinedPullback

noncomputable section

section

/-! Complex-linear pullback on the original native structure-sheaf H1
carries literal regular Čech cocycles to their original pulled sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

variable {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B) {I : Type} (U : I → B.left.Opens)
    (hU : iSup U = ⊤)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf).obj U 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf).obj U 1 k = 0)

theorem nativeStructureH1Pullback_cechClass :
    StructurePullback.nativeStructureH1Pullback f (StructureCechPullbackData.nativeStructureCechClass B.left U hU k hk) =
      StructureCechPullbackData.nativeStructureCechClass A.left (fun i => (TopologicalSpace.Opens.map f.left.base).obj (U i))
        (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU) (StructureCechPullbackData.structureCechPullback f.left U 1 k)
        (StructureCechPullbackData.structureCechPullback_closed f.left U 1 k hk) :=
  Intrinsic.CechSheafPullback.nativeCechSheafClass_pullback f.left.base U (StructurePullback.structureAdditivePullbackHom f.left)
    hU (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU) 0 k hk

theorem nativeStructureH1PullbackLinear_cechClass :
    StructurePullbackLinear.nativeStructureH1PullbackLinear f (StructureCechPullbackData.nativeStructureCechClass B.left U hU k hk) =
      StructureCechPullbackData.nativeStructureCechClass A.left (fun i => (TopologicalSpace.Opens.map f.left.base).obj (U i))
        (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU) (StructureCechPullbackData.structureCechPullback f.left U 1 k)
        (StructureCechPullbackData.structureCechPullback_closed f.left U 1 k hk) :=
  nativeStructureH1Pullback_cechClass f U hU k hk

end

/-! Refining the original pullback Cech cover gives the literal
ambient section maps and preserves the original native H1 class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {I J : Type}
    (U : I → Y.Opens) (V : J → X.Opens) (r : J → I) (hr : ∀ j, V j ≤ f ⁻¹ᵁ U (r j))

include hr

theorem cechMorphismIntersection_le {n : ℕ} (t : Fin (n + 1) → J) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V t ≤ f ⁻¹ᵁ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ t) := by
  intro x hx
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U (r ∘ t) (f x)).mpr
  intro i
  exact hr (t i) ((AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection V t x).mp hx i)

theorem structureCechRefinedPullback_apply (n : ℕ)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf Y.sheaf).obj U n) (t : Fin (n + 1) → J) :
    DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (fun i => f ⁻¹ᵁ U i) V r hr (Dual.UnitCechClasses.ringAdditiveSheaf X.sheaf).obj n
      (StructureCechPullbackData.structureCechPullback f U n k) t =
      f.appLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ t)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V t)
        (cechMorphismIntersection_le f U V r hr t) (k (r ∘ t)) := by
  change X.presheaf.map _ (X.presheaf.map _ (f.app _ (k (r ∘ t)))) =
    X.presheaf.map _ (f.app _ (k (r ∘ t)))
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 1

omit hr in
theorem nativeStructureCechClass_morphism {A B : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : A ⟶ B)
    {I J : Type} (U : I → B.left.Opens) (V : J → A.left.Opens) (r : J → I)
    (hr : ∀ j, V j ≤ f.left ⁻¹ᵁ U (r j)) (hU : iSup U = ⊤) (hV : iSup V = ⊤)
    (k : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf).obj U 1)
    (l : DivisorClass.Chern.Abelian.CechCoordinates.AbelianCechCochain (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf).obj V 1)
    (hk : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf B.left.sheaf).obj U 1 k = 0)
    (hl : DivisorClass.Chern.Abelian.CechCoordinates.abelianCechDelta (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf).obj V 1 l = 0)
    (he : ∀ t, l t = f.left.appLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ t)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V t)
      (cechMorphismIntersection_le f.left U V r hr t) (k (r ∘ t))) :
    StructureCechPullbackData.nativeStructureCechClass A.left V hV l hl =
      StructurePullback.nativeStructureH1Pullback f (StructureCechPullbackData.nativeStructureCechClass B.left U hU k hk) := by
  have hp := nativeStructureH1Pullback_cechClass f U hU k hk
  have hf := DivisorClass.Chern.Cech.ClassRefinement.abelianCechSheafClass_refinement (fun i => f.left ⁻¹ᵁ U i) V r hr
    (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf) (Inverse.ImageCechCover.inverseImageCechCover_covers f.left.base U hU) hV 0
    (StructureCechPullbackData.structureCechPullback f.left U 1 k) (StructureCechPullbackData.structureCechPullback_closed f.left U 1 k hk)
  have hc : l = DivisorClass.Chern.Cech.AbelianRefinement.abelianCechRefinementMap (fun i => f.left ⁻¹ᵁ U i) V r hr
      (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf).obj 1 (StructureCechPullbackData.structureCechPullback f.left U 1 k) := by
    funext t
    exact (he t).trans (structureCechRefinedPullback_apply f.left U V r hr 1 k t).symm
  exact (Cech.Add.cechSheafClass_congr V (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf) hV 0 l _ hl
    (DivisorClass.Chern.Cech.ClassRefinement.abelianCechRefinementMap_closed (fun i => f.left ⁻¹ᵁ U i) V r hr
      (Dual.UnitCechClasses.ringAdditiveSheaf A.left.sheaf).obj 1 _ (StructureCechPullbackData.structureCechPullback_closed f.left U 1 k hk)) hc).trans
        (hf.trans hp.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.StructureCechRefinedPullback
