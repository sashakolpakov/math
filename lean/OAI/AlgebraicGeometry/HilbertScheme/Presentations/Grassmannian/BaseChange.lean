import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Projectivity

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange

noncomputable section

/-!
The Grassmannian over any base is the scheme-theoretic base change of the
Grassmannian over its ring of global functions. More generally, its defining
square is Cartesian for every morphism of base schemes.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {ι ν : Type u} [Fintype ι] [DecidableEq ι]
variable {S T : Scheme.{u}} (f : T ⟶ S)

theorem grassmannianBaseMap_preimage_chart (a : ι → ν) :
    BaseMap.grassmannianBaseMap f ⁻¹ᵁ (Gluing.grassmannianChartMap a S).opensRange =
      (Gluing.grassmannianChartMap a T).opensRange := by
  have h (b : ι → ν) :
      Gluing.grassmannianChartMap b T ⁻¹ᵁ
        (BaseMap.grassmannianBaseMap f ⁻¹ᵁ (Gluing.grassmannianChartMap a S).opensRange) =
      Gluing.grassmannianChartMap b T ⁻¹ᵁ (Gluing.grassmannianChartMap a T).opensRange := by
    calc
      _ = (Gluing.grassmannianChartMap b T ≫ BaseMap.grassmannianBaseMap f) ⁻¹ᵁ
          (Gluing.grassmannianChartMap a S).opensRange := (Scheme.Hom.comp_preimage _ _ _).symm
      _ = (Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap b f ≫ Gluing.grassmannianChartMap b S) ⁻¹ᵁ
          (Gluing.grassmannianChartMap a S).opensRange :=
        congrArg (fun g => g ⁻¹ᵁ (Gluing.grassmannianChartMap a S).opensRange) (BaseMap.grassmannianBaseMap_chart f b)
      _ = _ := by
        rw [Scheme.Hom.comp_preimage, Plucker.ChartPreimages.Grassmannian.grassmannianChart_preimage_chart,
          Scheme.preimage_basicOpen_top, Normalized.OverlapBaseChange.Grassmannian.normalizedChartBaseMap_pivot, Plucker.ChartPreimages.Grassmannian.grassmannianChart_preimage_chart]
  ext x
  obtain ⟨b, y, rfl⟩ := Gluing.grassmannianCharts_cover T x
  exact (congrArg (fun U : (Normalized.Chart.Grassmannian.normalizedChart b T).left.Opens => y ∈ U) (h b)).to_iff

theorem grassmannianBaseMap_chart_isPullback (a : ι → ν) :
    IsPullback (Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f) (Gluing.grassmannianChartMap a T)
      (Gluing.grassmannianChartMap a S) (BaseMap.grassmannianBaseMap f) := by
  apply IsOpenImmersion.isPullback
  · exact BaseMap.grassmannianBaseMap_chart f a
  · exact grassmannianBaseMap_preimage_chart f a

theorem grassmannianBaseMap_isPullback :
    IsPullback (BaseMap.grassmannianBaseMap (ι := ι) (ν := ν) f) (Gluing.grassmannianStructureMap T)
      (Gluing.grassmannianStructureMap S) f := by
  apply Scheme.isPullback_of_openCover _ _ _ _
    (Gluing.normalizedGrassmannianGlueData (ι := ι) (ν := ν) S).openCover
  intro a
  change ι → ν at a
  let g := Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap a f
  let i := Gluing.grassmannianChartMap a T
  let j := Gluing.grassmannianChartMap a S
  let p := Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S
  let q := Gluing.grassmannianStructureMap (ι := ι) (ν := ν) T
  have H₁ : IsPullback g i j (BaseMap.grassmannianBaseMap f) := grassmannianBaseMap_chart_isPullback f a
  have H₂ : IsPullback g (i ≫ q) (j ≫ p) f := by
    dsimp only [i, j, p, q]
    rw [Gluing.grassmannianChartMap_structureMap, Gluing.grassmannianChartMap_structureMap]
    exact Normalized.ChartBaseChange.Grassmannian.normalizedChartBaseMap_isPullback a f
  apply H₂.of_iso H₁.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · change g ≫ 𝟙 _ = H₁.flip.isoPullback.hom ≫ pullback.snd (BaseMap.grassmannianBaseMap f) j
    rw [Category.comp_id]
    exact H₁.flip.isoPullback_hom_snd.symm
  · change (i ≫ q) ≫ 𝟙 _ =
      H₁.flip.isoPullback.hom ≫ pullback.fst (BaseMap.grassmannianBaseMap f) j ≫ q
    rw [Category.comp_id]
    exact (congrArg (fun h => h ≫ q) H₁.flip.isoPullback_hom_fst.symm).trans (Category.assoc _ _ _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · simp

def grassmannianBaseChangeIso : Gluing.grassmannianScheme (ι := ι) (ν := ν) T ≅
    pullback (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) f :=
  (grassmannianBaseMap_isPullback (ι := ι) (ν := ν) f).isoPullback

instance grassmannianStructureMap_proper (S : Scheme.{u}) [Finite ν] :
    IsProper (Gluing.grassmannianStructureMap (ι := ι) (ν := ν) S) :=
  MorphismProperty.of_isPullback (P := @IsProper)
    (grassmannianBaseMap_isPullback (ι := ι) (ν := ν) S.toSpecΓ)
    (Projectivity.grassmannianStructureMap_isProper Γ(S, ⊤))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.BaseChange
