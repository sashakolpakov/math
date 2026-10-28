import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Polarized.RetractionCarrier
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareCompatibilityComposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenProductData

/-! # Product Normalization From Poincare -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProductNormalizationFromPoincare

noncomputable section

/-! Poincare compatibility forces the dual comparison to induce the
identity on the actual special fiber whenever the abelian comparison does.
The reference comparison is the proved polarized pullback retraction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {S T : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
    (p : T ⟶ S) (r : S ⟶ T) (w : r ≫ p = 𝟙 S)
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T)
    (e : A.abelian.scheme ≅ ((A.abelian.pullback r).pullback p).scheme)
    (d : A.dual.abelian.scheme ≅ ((A.dual.abelian.pullback r).pullback p).scheme)

theorem retractionProduct_normalized_of_poincare (he : NormalizedDual.OpenProductData.NormalizesProductFiber (Over.pullback p) (Over.pullback r) (Pullback.RetractionIso.pullbackRetractionIso p r w) e)
    (hp : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf ((A.dual.pullback r).pullback p).poincare) =
        HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare) : NormalizedDual.OpenProductData.NormalizesProductFiber (Over.pullback p) (Over.pullback r) (Pullback.RetractionIso.pullbackRetractionIso p r w) d := by
  let A₀ := A.pullback r
  let B := A₀.pullback p
  let eB : A.abelian.scheme ≅ B.abelian.scheme := by
    dsimp only [B, A₀, HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
    exact e
  let dB : A.dual.abelian.scheme ≅ B.dual.abelian.scheme := by
    dsimp only [B, A₀, HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
    exact d
  have hpB : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (dB.hom ⊗ₘ eB.hom).left (HilbertConstruction.Line.Bundles.LineBundle.classOf B.dual.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf A.dual.poincare := by
    dsimp only [dB, eB, B, A₀, HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.pullback]
    exact hp
  let G := Over.pullback r
  let j := Polarized.PullbackRetraction.polarizedPullbackRetractionIso A₀ p r
    w
  have ha : j.abelian.hom = (Pullback.RetractionIso.pullbackRetractionIso p r w).hom.app A₀.abelian.scheme :=
    Polarized.RetractionCarrier.polarizedRetraction_abelian A₀ p r
      w
  have hd : j.dual.hom = (Pullback.RetractionIso.pullbackRetractionIso p r w).hom.app A₀.dual.abelian.scheme :=
    Polarized.RetractionCarrier.polarizedRetraction_dual A₀ p r
      w
  have hr := HilbertConstruction.Poincare.CompatibilityBaseChange.poincareCompatibility_pullback A.dual B.dual dB.hom eB.hom hpB r
  have H := PoincareCompatibilityComposition.poincareCompatibility_comp A₀.dual (B.pullback r).dual A₀.dual
    (G.map dB.hom) (G.map eB.hom) j.dual.hom j.abelian.hom hr j.poincare
  let v : A₀.abelian.scheme ⟶ A₀.abelian.scheme := G.map eB.hom ≫ j.abelian.hom
  let q : A₀.dual.abelian.scheme ⟶ A₀.dual.abelian.scheme := G.map dB.hom ≫ j.dual.hom
  have he' : v = 𝟙 A₀.abelian.scheme := by
    dsimp only [v]
    rw [ha]
    exact he
  have H₀ : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (q ⊗ₘ v).left (HilbertConstruction.Line.Bundles.LineBundle.classOf A₀.dual.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf A₀.dual.poincare := H
  rw [he'] at H₀
  have hi : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((𝟙 A₀.dual.abelian.scheme) ⊗ₘ (𝟙 A₀.abelian.scheme)).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf A₀.dual.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf A₀.dual.poincare := by
    rw [tensorHom_id, id_whiskerRight, Over.id_left, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  have h := A₀.dual.hom_eq_of_poincarePullbackClass q (𝟙 A₀.dual.abelian.scheme) (H₀.trans hi.symm)
  dsimp only [q] at h
  rw [hd] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProductNormalizationFromPoincare
