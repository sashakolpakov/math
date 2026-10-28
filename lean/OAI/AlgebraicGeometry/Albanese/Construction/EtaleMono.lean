import OAI.AlgebraicGeometry.Albanese.Construction.EtaleGeneric
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Etale Mono -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.EtaleMono

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- For an étale map from a smooth separated complex scheme, injectivity on
complex points implies categorical monomorphism. The pullback is reduced,
so its two projections can be compared on complex points. -/
theorem etale_mono_of_point_injective (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [Smooth X.hom] [IsSeparated X.hom] (f : X ⟶ Y) [Etale f.left]
    (hinj : Function.Injective (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X => p ≫ f)) :
    Mono f.left := by
  let P : Over Foundations.Scheme.ProjectiveSpace.complexBase := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  have hbase : pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom := by
    rw [← f.w, ← Category.assoc, ← Category.assoc, pullback.condition]
  let p₁ : P ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let p₂ : P ⟶ X := Over.homMk (pullback.snd f.left f.left) hbase
  have : Smooth P.hom := by dsimp [P]; infer_instance
  have : IsReduced P.left := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced P.hom
  have hproj : p₁ ≫ f = p₂ ≫ f := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have hp : p₁ = p₂ := by
    apply ClosedPoints.hom_ext_of_points P X p₁ p₂
    intro p
    apply hinj
    simpa only [Category.assoc] using congrArg (fun k => p ≫ k) hproj
  have hp' : pullback.fst f.left f.left = pullback.snd f.left f.left := congrArg Over.Hom.left hp
  refine ⟨fun {Z} g h heq => ?_⟩
  calc
    g = pullback.lift g h heq ≫ pullback.fst f.left f.left := by simp
    _ = pullback.lift g h heq ≫ pullback.snd f.left f.left := by rw [hp']
    _ = h := by simp

/-- An étale surjection between complex abelian varieties which is injective
on complex points is an isomorphism of the actual schemes over the base. -/
theorem abelian_etale_isIso_of_point_injective (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : A.toOver ⟶ B.toOver) [Etale f.left] [Surjective f.left]
    (hinj : Function.Injective (fun p : Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ A.toOver => p ≫ f)) :
    IsIso f := by
  have : Smooth A.toOver.hom := A.variety.presentation.smooth
  have : IsProper A.toOver.hom := A.variety.presentation.projective.isProper
  have : IsProper B.toOver.hom := B.variety.presentation.projective.isProper
  have : IsProper (f.left ≫ B.toOver.hom) := by rw [f.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp _ B.toOver.hom
  have : Mono f.left := etale_mono_of_point_injective A.toOver B.toOver f hinj
  have : IsClosedImmersion f.left :=
    (IsClosedImmersion.iff_isProper_and_mono f.left).mpr ⟨inferInstance, inferInstance⟩
  have : IsReduced B.toOver.left := inferInstanceAs (IsReduced B.carrier)
  have : IsIso f.left := isIso_of_isClosedImmersion_of_surjective f.left
  have : IsIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).map f) := inferInstanceAs (IsIso f.left)
  exact isIso_of_reflects_iso f (Over.forget _)

end

end OAI.AlgebraicGeometry.Albanese.Construction.EtaleMono
