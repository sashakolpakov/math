import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyOpenCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubterminalRelativeChart
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Sheaf Open Cover Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafOpenCoverDetection

noncomputable section

/-! Open-cover detection for the actual fppf sheaves on schemes over a
fixed base. The tests themselves are arbitrary schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u v

variable {S : Scheme.{u}}

theorem fppf_openCover_sieve_mem (T : Over S) (C : T.left.OpenCover.{u}) :
    Sieve.ofArrows (fun i => Embedded.FamilyOpenCover.overOpenCoverObject T C i) (fun i => Embedded.FamilyOpenCover.overOpenCoverMap T C i) ∈
      (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
    _ C.mem_grothendieckTopology

theorem fppfSheaf_eq_of_openCover
    (F : Sheaf (Scheme.fppfTopology.over S) (Type v)) (T : Over S) (C : T.left.OpenCover.{u})
    (a b : F.obj.obj (.op T))
    (h : ∀ i, F.obj.map (Embedded.FamilyOpenCover.overOpenCoverMap T C i).op a = F.obj.map (Embedded.FamilyOpenCover.overOpenCoverMap T C i).op b) :
    a = b := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (hF _ (fppf_openCover_sieve_mem T C)).isSeparatedFor.ext
  intro U f hf
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
  rw [hk, op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply, h i]

theorem fppf_baseOpenCover_sieve_mem (C : S.OpenCover.{u}) (T : Over S) :
    Sieve.ofArrows (fun i => SubterminalRelativeChart.baseChartTest (C.f i) T) (fun i => SubterminalRelativeChart.baseChartProjection (C.f i) T) ∈
      (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage)
    _ (Scheme.Cover.mem_grothendieckTopology (C.pullback₁ T.hom))

theorem fppfSheaf_eq_of_baseOpenCover
    (F : Sheaf (Scheme.fppfTopology.over S) (Type v)) (C : S.OpenCover.{u}) (T : Over S)
    (a b : F.obj.obj (.op T))
    (h : ∀ i, F.obj.map (SubterminalRelativeChart.baseChartProjection (C.f i) T).op a =
      F.obj.map (SubterminalRelativeChart.baseChartProjection (C.f i) T).op b) : a = b := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  apply (hF _ (fppf_baseOpenCover_sieve_mem C T)).isSeparatedFor.ext
  intro U f hf
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff _ _ f).mp hf
  rw [hk, op_comp, F.obj.map_comp_apply, F.obj.map_comp_apply, h i]

variable (C : S.OpenCover.{u}) {F G : Sheaf (Scheme.fppfTopology.over S) (Type v)}
  (a : F ⟶ G)
  (ha : ∀ i (T : Over (C.X i)),
    Function.Bijective (a.hom.app (.op ((Over.map (C.f i)).obj T))))

include ha in
theorem fppfSheaf_app_injective_of_baseOpenCover (T : Over S) :
    Function.Injective (a.hom.app (.op T)) := by
  intro x y hxy
  apply fppfSheaf_eq_of_baseOpenCover F C T x y
  intro i
  apply (ha i ((Over.pullback (C.f i)).obj T)).injective
  exact (a.hom.naturality_apply (SubterminalRelativeChart.baseChartProjection (C.f i) T).op x).trans
    ((congrArg (G.obj.map (SubterminalRelativeChart.baseChartProjection (C.f i) T).op) hxy).trans
      (a.hom.naturality_apply (SubterminalRelativeChart.baseChartProjection (C.f i) T).op y).symm)

include ha in
theorem fppfSheaf_locallySurjective_of_baseOpenCover : Sheaf.IsLocallySurjective a where
  imageSieve_mem {T} x := by
    apply (Scheme.fppfTopology.over S).superset_covering _ (fppf_baseOpenCover_sieve_mem C T)
    apply (Sieve.generate_le_iff _ _).mpr
    rintro U f ⟨i⟩
    exact (ha i ((Over.pullback (C.f i)).obj T)).surjective
      (G.obj.map (SubterminalRelativeChart.baseChartProjection (C.f i) T).op x)

include ha in
theorem fppfSheaf_isIso_of_baseOpenCover : IsIso a := by
  have hinj : Sheaf.IsLocallyInjective a :=
    (Sheaf.isLocallyInjective_iff_injective a).mpr
      (fun T => fppfSheaf_app_injective_of_baseOpenCover C a ha T.unop)
  exact (Sheaf.isLocallyBijective_iff_isIso a).mp
    ⟨hinj, fppfSheaf_locallySurjective_of_baseOpenCover C a ha⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafOpenCoverDetection
