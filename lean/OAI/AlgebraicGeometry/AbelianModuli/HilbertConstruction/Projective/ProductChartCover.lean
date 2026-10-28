import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveChartOver
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.ProductCharts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts

/-! # Product Chart Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductChartCover

noncomputable section

/-! The actual affine product charts cover the product of two projective spaces. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ} (p : Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

def projectiveProductChart : Scheme.{u} :=
  pullback (StandardProjectiveChartOver.projectiveStandardChartOver R n p.1.down).hom (StandardProjectiveChartOver.projectiveStandardChartOver R m p.2.down).hom

def projectiveProductChartMap : projectiveProductChart R p ⟶
    pullback (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom :=
  pullback.map _ _ _ _ (StandardProjectiveChartOver.projectiveStandardChartInclusion R n p.1.down)
    (StandardProjectiveChartOver.projectiveStandardChartInclusion R m p.2.down) (𝟙 (Spec R))
    ((Category.comp_id _).trans (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R n p.1.down).symm)
    ((Category.comp_id _).trans (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R m p.2.down).symm)

instance projectiveProductChartMap_isOpenImmersion : IsOpenImmersion (projectiveProductChartMap R p) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R n p.1.down).symm
    (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R m p.2.down).symm

theorem projectiveProductChartMap_fst :
    projectiveProductChartMap R p ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ StandardProjectiveChartOver.projectiveStandardChartInclusion R n p.1.down := pullback.lift_fst _ _ _

theorem projectiveProductChartMap_snd :
    projectiveProductChartMap R p ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ StandardProjectiveChartOver.projectiveStandardChartInclusion R m p.2.down := pullback.lift_snd _ _ _

theorem projectiveProductChartMap_opensRange :
    (projectiveProductChartMap R p).opensRange =
      (pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom ⁻¹ᵁ
        Proj.basicOpen (ProjectivePresentations.coordinateGrading R n) (X p.1.down)) ⊓
      (pullback.snd (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom ⁻¹ᵁ
        Proj.basicOpen (ProjectivePresentations.coordinateGrading R m) (X p.2.down)) := by
  let a := StandardProjectiveChartOver.projectiveStandardChartInclusion R n p.1.down
  let b := StandardProjectiveChartOver.projectiveStandardChartInclusion R m p.2.down
  let f := (ProjectivePresentations.affineProjectiveSpace R n).hom
  let g := (ProjectivePresentations.affineProjectiveSpace R m).hom
  let e := pullback.congrHom (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R n p.1.down).symm
    (StandardProjectiveChartOver.projectiveStandardChartInclusion_over R m p.2.down).symm
  have hfst : e.hom ≫ pullback.fst (a ≫ f) (b ≫ g) =
      pullback.fst (StandardProjectiveChartOver.projectiveStandardChartOver R n p.1.down).hom
        (StandardProjectiveChartOver.projectiveStandardChartOver R m p.2.down).hom :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hsnd : e.hom ≫ pullback.snd (a ≫ f) (b ≫ g) =
      pullback.snd (StandardProjectiveChartOver.projectiveStandardChartOver R n p.1.down).hom
        (StandardProjectiveChartOver.projectiveStandardChartOver R m p.2.down).hom :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have he : e.hom ≫ Open.ProductCharts.openProductChartMap f g a b = projectiveProductChartMap R p := by
    apply pullback.hom_ext
    · exact (Category.assoc e.hom (Open.ProductCharts.openProductChartMap f g a b) (pullback.fst f g)).trans
        ((congrArg (fun k => e.hom ≫ k) (Open.ProductCharts.openProductChartMap_fst f g a b)).trans
          ((Category.assoc e.hom (pullback.fst (a ≫ f) (b ≫ g)) a).symm.trans
            ((congrArg (fun k => k ≫ a) hfst).trans (projectiveProductChartMap_fst R p).symm)))
    · exact (Category.assoc e.hom (Open.ProductCharts.openProductChartMap f g a b) (pullback.snd f g)).trans
        ((congrArg (fun k => e.hom ≫ k) (Open.ProductCharts.openProductChartMap_snd f g a b)).trans
          ((Category.assoc e.hom (pullback.snd (a ≫ f) (b ≫ g)) b).symm.trans
            ((congrArg (fun k => k ≫ b) hsnd).trans (projectiveProductChartMap_snd R p).symm)))
  have h₀ : (projectiveProductChartMap R p).opensRange = (e.hom ≫ Open.ProductCharts.openProductChartMap f g a b).opensRange :=
    TopologicalSpace.Opens.ext (congrArg (fun h : projectiveProductChart R p ⟶ pullback f g => Set.range h) he.symm)
  have h := h₀.trans
    ((Scheme.Hom.opensRange_comp_of_isIso e.hom (Open.ProductCharts.openProductChartMap f g a b)).trans
      (Open.ProductCharts.openProductChartMap_opensRange f g a b))
  exact h.trans (congrArg₂ (fun U V => (pullback.fst f g ⁻¹ᵁ U) ⊓ (pullback.snd f g ⁻¹ᵁ V))
    (StandardProjectiveChartOver.projectiveStandardChartInclusion_opensRange R n p.1.down)
    (StandardProjectiveChartOver.projectiveStandardChartInclusion_opensRange R m p.2.down))

theorem projectiveProductCharts_cover
    (x : (pullback (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom : Scheme.{u})) :
    ∃ p : Segre.ChartProjections.SegreProjectiveIndex.{u} n m, ∃ y : projectiveProductChart R p,
      projectiveProductChartMap R p y = x := by
  obtain ⟨i, hi⟩ := StandardProjectiveCharts.standardProjectiveCharts_cover R n
    (pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom x)
  obtain ⟨j, hj⟩ := StandardProjectiveCharts.standardProjectiveCharts_cover R m
    (pullback.snd (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom x)
  let p : Segre.ChartProjections.SegreProjectiveIndex.{u} n m := (ULift.up i, ULift.up j)
  have hx : x ∈ (projectiveProductChartMap R p).opensRange :=
    (congrArg (fun U => x ∈ U) (projectiveProductChartMap_opensRange R p)).mpr ⟨hi, hj⟩
  exact ⟨p, hx⟩

def projectiveProductOpenCover (n m : ℕ) :
    (pullback (ProjectivePresentations.affineProjectiveSpace R n).hom (ProjectivePresentations.affineProjectiveSpace R m).hom).OpenCover where
  I₀ := Segre.ChartProjections.SegreProjectiveIndex.{u} n m
  X p := projectiveProductChart R p
  f p := projectiveProductChartMap R p
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨projectiveProductCharts_cover R, inferInstance⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductChartCover
