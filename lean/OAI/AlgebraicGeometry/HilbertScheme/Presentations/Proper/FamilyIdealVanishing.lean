import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.AffineParameterLocus
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterAffineGluing

/-! # Family Ideal Vanishing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FamilyIdealVanishing.Core

noncomputable section

/-! Vanishing of an arbitrary ideal on a proper flat source is represented
by a closed subscheme of every locally Noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (X : Over S) [Flat X.hom] [IsProper X.hom]
variable {B : Over S} [IsLocallyNoetherian B.left]

theorem proper_family_ideal_vanishing_closed_locus
    (K : (Hilbert.Functor.ambient X B).IdealSheafData) :
    ∃ (Z : Over S) (j : Z ⟶ B), IsClosedImmersion j.left ∧
      (∀ (T : Over S) (x : T ⟶ B), K.comap (Hilbert.Functor.ambientMap X x) = ⊥ ↔
        ∃! y : T ⟶ Z, y ≫ j = x) ∧
      ∃ e : yoneda.obj Z ≅ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).toFunctor,
        e.hom ≫ (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥).ι = yoneda.map j := by
  let F := Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor X K ⊥
  have hlocal : ∀ (T : Over S) (D : T.left.OpenCover.{u}) (x : T ⟶ B),
      (∀ i, (Over.homMk (D.f i) rfl : Over.mk (D.f i ≫ T.hom) ⟶ T) ≫ x ∈
        F.obj (.op (Over.mk (D.f i ≫ T.hom)))) → x ∈ F.obj (.op T) := by
    intro T D x h
    let V (i : D.I₀) : Over S := Over.mk (D.f i ≫ T.hom)
    let v (i : D.I₀) : V i ⟶ T := Over.homMk (D.f i) rfl
    let : ∀ i, IsOpenImmersion (v i).left := fun i => inferInstanceAs (IsOpenImmersion (D.f i))
    exact Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameter_of_openCover X K ⊥ V v
      (fun t => D.exists_eq t) x h
  have hcharts : ∀ i : B.left.affineOpenCover.I₀,
      ∃ (Z : Over S) (j : Z ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i), IsClosedImmersion j.left ∧
        ∀ (T : Over S) (x : T ⟶ Intrinsic.ContainmentAffineCharts.affineParameterChart B i),
          x ≫ Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B i ∈ F.obj (.op T) ↔
            ∃! y : T ⟶ Z, y ≫ j = x := by
    intro i
    let R := B.left.affineOpenCover.X i
    let : IsNoetherianRing R := Intrinsic.ContainmentAffineCharts.affineParameterChart_noetherian B i
    let u := Intrinsic.ContainmentAffineCharts.affineParameterChartInclusion B i
    obtain ⟨Z, j, hj, ht, _⟩ := AffineParameterLocus.proper_affine_parameter_locus X R
      (B.left.affineOpenCover.f i ≫ B.hom) (K.comap (Hilbert.Functor.ambientMap X u))
    refine ⟨Z, j, hj, fun T x => ?_⟩
    have he := Ideal.ContainmentParameterBaseChange.Hilbert.idealContainmentParameter_baseChange X K ⊥ u x
    rw [Scheme.IdealSheafData.comap_bot] at he
    refine he.symm.trans ?_
    change (K.comap (Hilbert.Functor.ambientMap X u)).comap (Hilbert.Functor.ambientMap X x) ≤
      (⊥ : (Hilbert.Functor.ambient X (Intrinsic.ContainmentAffineCharts.affineParameterChart B i)).IdealSheafData).comap
        (Hilbert.Functor.ambientMap X x) ↔ _
    rw [Scheme.IdealSheafData.comap_bot, le_bot_iff]
    exact ht T x
  obtain ⟨Z, j, hj, ht⟩ := Closed.ParameterAffineGluing.closed_parameter_of_affine_charts B F hlocal hcharts
  let : IsClosedImmersion j.left := hj
  let : Mono j := Over.mono_of_mono_left j
  refine ⟨Z, j, hj, ?_, ?_⟩
  · intro T x
    have h := ht T x
    change K.comap (Hilbert.Functor.ambientMap X x) ≤
      (⊥ : (Hilbert.Functor.ambient X B).IdealSheafData).comap (Hilbert.Functor.ambientMap X x) ↔ _ at h
    simpa only [Scheme.IdealSheafData.comap_bot, le_bot_iff] using h
  · apply SubfunctorRepresentations.subfunctor_representation_of_lifts F j
    intro T x
    constructor
    · exact fun h => ((ht T x).mp h).exists
    · rintro ⟨y, hy⟩
      exact (ht T x).mpr ⟨y, hy, fun z hz => (cancel_mono j).mp (hz.trans hy.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Proper.FamilyIdealVanishing.Core
