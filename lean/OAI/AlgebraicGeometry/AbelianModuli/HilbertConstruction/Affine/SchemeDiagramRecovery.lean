import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.OverMorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.DiagramSchemes

/-! # Scheme Diagram Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramRecovery

noncomputable section

/-! Smooth coordinate-diagram models recover the actual affine schemes and their arrows. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {I : Type v} (X : I → Over (Spec (.of R)))
variable [∀ i, IsAffine (X i).left]
variable {J : Type w} (s t : J → I) (f : ∀ j, X (t j) ⟶ X (s j))
variable (M : Smooth.AffineDiagramModel.SmoothAffineDiagramModel R (fun i => ↥(OverChartPoints.affineOverAlgebra R (X i))) s t
  (fun j => OverMorphisms.affineOverMap R (f j)))

def affineDiagramModelMap (i : I) : (X i).left ⟶ M.chartScheme i :=
  (OverChartPoints.affineOverIso R (X i)).hom.left ≫ M.realizationSpec i

theorem affineDiagramModel_isPullback (i : I) :
    IsPullback (affineDiagramModelMap X s t f M i) (X i).hom (M.chartMap i)
      (Spec.map (CommRingCat.ofHom M.coefficients.val.toRingHom)) := by
  let e := OverChartPoints.affineOverIso R (X i)
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have H : IsPullback e.hom.left (X i).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R (OverChartPoints.affineOverAlgebra R (X i)))))
      (𝟙 (Spec (.of R))) := IsPullback.of_horiz_isIso ⟨e.hom.w.trans (Category.comp_id _).symm⟩
  have h := H.paste_horiz (M.realizationSpec_isPullback i)
  exact (congrArg (fun b => IsPullback (affineDiagramModelMap X s t f M i) (X i).hom (M.chartMap i) b)
    (Category.id_comp _)).mp h

theorem affineDiagramModel_natural (j : J) :
    affineDiagramModelMap X s t f M (t j) ≫ M.chartArrow j =
      (f j).left ≫ affineDiagramModelMap X s t f M (s j) := by
  let e : (X (t j)).left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra R (X (t j)))) :=
    (OverChartPoints.affineOverIso R (X (t j))).hom.left
  let d : Spec (.of (OverChartPoints.affineOverAlgebra R (X (t j)))) ⟶ (X (t j)).left :=
    (OverChartPoints.affineOverIso R (X (t j))).inv.left
  let e' : (X (s j)).left ⟶ Spec (.of (OverChartPoints.affineOverAlgebra R (X (s j)))) :=
    (OverChartPoints.affineOverIso R (X (s j))).hom.left
  have he : e ≫ d = 𝟙 (X (t j)).left :=
    congrArg (fun k => k.left) (OverChartPoints.affineOverIso R (X (t j))).hom_inv_id
  have hf : Spec.map (CommRingCat.ofHom (OverMorphisms.affineOverMap R (f j)).toRingHom) =
      d ≫ (f j).left ≫ e' := OverMorphisms.affineOverMap_spec R (f j)
  change (e ≫ M.realizationSpec (t j)) ≫ M.chartArrow j =
    (f j).left ≫ (e' ≫ M.realizationSpec (s j))
  rw [Category.assoc, M.realizationSpec_natural, hf]
  simp only [← Category.assoc, he, Category.id_comp]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SchemeDiagramRecovery
