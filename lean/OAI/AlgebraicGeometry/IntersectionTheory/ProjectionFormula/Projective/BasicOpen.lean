import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart
import Mathlib.AlgebraicGeometry.Gluing

/-! # Basic Open -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen

noncomputable section

section

/-! A graded homogeneous-coordinate map gives an actual projective
scheme morphism outside the common zero locus of its coordinate forms.
The local maps are glued by the proved homogeneous-localization identities. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace RationalProjection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Hom

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

abbrev coordinateOpen (i : Fin (m + 1)) : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens :=
  Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f (MvPolynomial.X i))

abbrev domain : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Opens := ⨆ i, coordinateOpen f i

abbrev cover : (domain f).toScheme.OpenCover := Scheme.Opens.iSupOpenCover (coordinateOpen f)

theorem compatible (i j : Fin (m + 1)) :
    pullback.fst ((cover f).f i) ((cover f).f j) ≫
      LinearChart.Hom.chart f (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one =
    pullback.snd ((cover f).f i) ((cover f).f j) ≫
      LinearChart.Hom.chart f (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) Nat.zero_lt_one := by
  change pullback.fst ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) i))
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) j)) ≫
      LinearChart.Hom.chart f (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one =
    pullback.snd ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) i))
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) j)) ≫
      LinearChart.Hom.chart f (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X ℂ j) Nat.zero_lt_one
  let h := isPullback_opens_inf_le (le_iSup (coordinateOpen f) i) (le_iSup (coordinateOpen f) j)
  apply (cancel_epi h.isoPullback.hom).mp
  rw [← Category.assoc, h.isoPullback_hom_fst, ← Category.assoc, h.isoPullback_hom_snd]
  exact LinearChart.Overlap.agree f (MvPolynomial.X i) (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X ℂ i) (MvPolynomial.isHomogeneous_X ℂ j)
    Nat.zero_lt_one Nat.zero_lt_one (coordinateOpen f i ⊓ coordinateOpen f j) inf_le_left inf_le_right

def map : (domain f).toScheme ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  (cover f).glueMorphisms
    (fun i => LinearChart.Hom.chart f (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one)
    (compatible f)

theorem chart_map (i : Fin (m + 1)) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) i) ≫ RationalProjection.map f =
      LinearChart.Hom.chart f (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one :=
  (cover f).ι_glueMorphisms _ _ i

theorem over_base (hC : ∀ z : ℂ, f (MvPolynomial.C z) = MvPolynomial.C z) :
    RationalProjection.map f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = (domain f).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n := by
  apply (cover f).hom_ext
  intro i
  change (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) i) ≫
    (RationalProjection.map f ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) =
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (coordinateOpen f) i) ≫
      ((domain f).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  rw [← Category.assoc, chart_map, LinearChart.Hom.chart_over_base f hC,
    ← Category.assoc, Scheme.homOfLE_ι]

def linear {A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ} :
    (domain (LinearChart.Coordinates.gradedHom A)).toScheme ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m :=
  RationalProjection.map (LinearChart.Coordinates.gradedHom A)

theorem linear_over_base (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    linear (A := A) ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m =
      (domain (LinearChart.Coordinates.gradedHom A)).ι ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n :=
  over_base _ (fun z => LinearChart.Coordinates.algebraHom_C A z)

end RationalProjection

end

/-! The glued projection pulls back homogeneous basic opens by the
original graded coordinate homomorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Hom OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

theorem affine_preimage (s t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) (he : 0 < e) :
    LinearChart.Hom.affine f s hs hd ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t =
      Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd ⁻¹ᵁ
        Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t) := by
  change Spec.map (CommRingCat.ofHom (Away.map f s)) ⁻¹ᵁ
    (Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) s hs hd ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t) = _
  have h₁ := Proj.awayι_preimage_basicOpen (𝒜 := Foundations.Scheme.ProjectiveSpace.projectiveGrading m) hs hd ht he
  have h₂ := Proj.awayι_preimage_basicOpen (𝒜 := Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f.map_mem hs) hd (f.map_mem ht) he
  refine (congrArg (fun U => Spec.map (CommRingCat.ofHom (Away.map f s)) ⁻¹ᵁ U) h₁).trans (Eq.trans ?_ h₂.symm)
  change PrimeSpectrum.basicOpen (Away.map f s (Away.isLocalizationElem hs ht)) =
    PrimeSpectrum.basicOpen (Away.isLocalizationElem (f.map_mem hs) (f.map_mem ht))
  simp only [Away.isLocalizationElem, Away.map_mk, map_pow]
  rfl

theorem chart_preimage (s t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {d e : ℕ}
    (hs : s ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m d) (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (hd : 0 < d) (he : 0 < e) :
    LinearChart.Hom.chart f s hs hd ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t =
      (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s)).ι ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t) := by
  change (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd).hom ⁻¹ᵁ
    (LinearChart.Hom.affine f s hs hd ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t) = _
  rw [affine_preimage f s t hs ht hd he]
  have hi : (Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd).hom ≫
      Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s) (f.map_mem hs) hd =
      (Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f s)).ι := by
    simp only [Proj.awayι, Iso.hom_inv_id_assoc]
  ext x
  exact (congrArg (fun k => k x ∈ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t)) hi).to_iff

theorem preimage_basicOpen (t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing m) {e : ℕ}
    (ht : t ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading m e) (he : 0 < e) :
    RationalProjection.map f ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t =
      (RationalProjection.domain f).ι ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t) := by
  ext x
  obtain ⟨i, y, rfl⟩ := (RationalProjection.cover f).exists_eq x
  change (((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (RationalProjection.coordinateOpen f) i) ≫ RationalProjection.map f) y ∈
    Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading m) t) ↔
    (((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (RationalProjection.coordinateOpen f) i) ≫ (RationalProjection.domain f).ι) y ∈
      Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f t))
  rw [RationalProjection.chart_map, Scheme.homOfLE_ι]
  exact (congrArg (fun U => y ∈ U)
    (chart_preimage f (MvPolynomial.X i) t (MvPolynomial.isHomogeneous_X ℂ i) ht Nat.zero_lt_one he)).to_iff

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen
