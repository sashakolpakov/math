import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SquarePullbackGlobalFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareComposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareCongruence

/-! # Frame Pullback Cube -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FramePullbackCube

noncomputable section

/-! A normalized local frame stays normalized under an actual
commuting cube, with all module-pullback comparisons retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem normalizedFrame_pullback_cube {X Y X₀ Y₀ U V U₀ V₀ : Scheme.{0}}
    (F : X ⟶ Y) (rX : X₀ ⟶ X) (rY : Y₀ ⟶ Y) (f : X₀ ⟶ Y₀)
    (hg : f ≫ rY = rX ≫ F)
    (i : V ⟶ X) (j : U ⟶ Y) (p : V ⟶ U) (hp : p ≫ j = i ≫ F)
    (i₀ : V₀ ⟶ X₀) (j₀ : U₀ ⟶ Y₀) (p₀ : V₀ ⟶ U₀) (hp₀ : p₀ ≫ j₀ = i₀ ≫ f)
    (rV : V₀ ⟶ V) (rU : U₀ ⟶ U)
    (hX : rV ≫ i = i₀ ≫ rX) (hY : rU ≫ j = j₀ ≫ rY) (hc : rV ≫ p = p₀ ≫ rU)
    (M : Y.Modules) (e₀ : (Scheme.Modules.pullback rY).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y₀)
    (e : (Scheme.Modules.pullback j).obj M ≅ SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U)
    (he : RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame rY j₀ j rU hY M e = RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame j₀ e₀) :
    RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame rX i₀ i rV hX ((Scheme.Modules.pullback F).obj M)
        (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame F i j p hp M e) =
      RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame i₀ (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame F rX rY f hg M e₀) := by
  have hA : (rV ≫ p) ≫ j = i₀ ≫ (rX ≫ F) := by
    rw [Category.assoc, hp, ← Category.assoc, hX, Category.assoc]
  have hB : (p₀ ≫ rU) ≫ j = i₀ ≫ (f ≫ rY) := by
    rw [Category.assoc, hY, ← Category.assoc, hp₀, Category.assoc]
  have h₁ := Pullback.SquareComposition.pullbackSquareFrame_horizontal rX F i₀ i j rV p hX hp hA M e
  have h₂ := Pullback.SquareComposition.pullbackSquareFrame_horizontal f rY i₀ j₀ j p₀ rU hp₀ hY hB M e
  rw [he, SquarePullbackGlobalFrames.squarePullbackGlobalFrame] at h₂
  have h₃ := Pullback.SquareCongruence.pullbackSquareFrame_congr hg.symm i₀ j hc hA hB M e
  let B := (Scheme.Modules.pullback i₀).mapIso ((Scheme.Modules.pullbackComp f rY).app M)
  have h₄ : RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (f ≫ rY) i₀ j (p₀ ≫ rU) hB M e =
      B.symm ≪≫ RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame i₀ (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackGlobalFrame f e₀) :=
    (Iso.symm_self_id_assoc B _).symm.trans (congrArg (fun q => B.symm ≪≫ q) h₂.symm)
  rw [h₁, h₃, h₄]
  simp only [RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame, RepresentationTheory.Theta.Geometric.FactoredPullbackFrames.factoredPullbackFrame,
    SquarePullbackGlobalFrames.pullbackGlobalFrame_precomp, Functor.mapIso_symm, B]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.FramePullbackCube
