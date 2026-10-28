import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartCover
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Target Properties -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.TargetProperties

noncomputable section

/-! Properties local on the target can be checked on the actual pullbacks of the normalized Grassmann atlas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S : Scheme.{u}} {M : Over S}

theorem grassmannTarget_property (f : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
    (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget W]
    (hW : ∀ a : ι → ν, W (pullback.snd f (HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S)).left) : W f.left := by
  let C := ChartCover.grassmannParameterOpenCover (ι := ι) (ν := ν) S
  apply IsZariskiLocalAtTarget.of_openCover (P := W) C
  intro a
  change ι → ν at a
  let j := HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S
  have h : IsPullback (pullback.fst f j).left (pullback.snd f j).left f.left j.left :=
    (IsPullback.of_hasPullback f j).map (Over.forget S)
  have hh : W (h.isoPullback.inv ≫ (pullback.snd f j).left) :=
    (W.cancel_left_of_respectsIso _ _).mpr (hW a)
  have he : h.isoPullback.inv ≫ (pullback.snd f j).left = C.pullbackHom f.left a :=
    h.isoPullback_inv_snd
  exact he ▸ hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.TargetProperties
