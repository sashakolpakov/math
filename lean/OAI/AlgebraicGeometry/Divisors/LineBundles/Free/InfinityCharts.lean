import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.BasisSourceCharts
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.DeformationProperties

/-! # Infinity Charts -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts.BundleCycles
open _root_.AlgebraicGeometry
open _root_.CategoryTheory
section

/-! Actual finite free projective charts transfer target-local
geometric properties to the global projection. -/

theorem freeInfinityCharts_property (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ (R M ι : Type) [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι],
      Module.Basis ι R M → P (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M)))
    {E X : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L) : P p := by
  let C (x : X) := Classical.choice (H x)
  let V : X.OpenCover := Scheme.Cover.mkOfCovers X (fun x => Spec (C x).coefficient)
    (fun x => (C x).baseMap) (fun x => ⟨x, (C x).contains⟩) (fun x => (C x).open_base)
  exact Global.DeformationProperties.BundleCycles.morphismProperty_of_cover_pullbacks P p V
    (fun x => SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme (C x).coefficient ((C x).coefficient × (C x).module))
    (fun x => (C x).totalMap)
    (fun x => SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase (C x).coefficient ((C x).coefficient × (C x).module))
    (fun x => (C x).square) (fun x => hP (C x).coefficient (C x).module (Fin (C x).rank) (C x).basis)

theorem freeInfinityCharts_smooth {E X : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L) : Smooth p := by
  let : IsZariskiLocalAtTarget (@Smooth.{0}) := HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact freeInfinityCharts_property (@Smooth) (fun _R _M _ι _ _ _ _ b =>
    (Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts b).forget.smooth) p L H

theorem freeInfinityCharts_geometricallyIntegral {E X : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L) : GeometricallyIntegral p :=
  freeInfinityCharts_property (@GeometricallyIntegral)
    (fun _R _M _ι _ _ _ _ b => Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_geometricallyIntegral b) p L H

end

/-! A specified constant rank of actual projective infinity
charts gives source affine-space charts of that same rank. -/

def HasFreeProjectiveInfinityChartsOfRank {E X : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (r : ℕ) : Prop :=
  ∀ x : X, ∃ C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L x, C.rank = r

theorem HasFreeProjectiveInfinityChartsOfRank.forget {E X : Scheme.{0}}
    {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {r : ℕ} (H : HasFreeProjectiveInfinityChartsOfRank p L r) :
    ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L := by
  intro x
  obtain ⟨C, _⟩ := H x
  exact ⟨C⟩

theorem HasFreeProjectiveInfinityChartsOfRank.sourceCharts {E X : Scheme.{0}}
    {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {r : ℕ} (H : HasFreeProjectiveInfinityChartsOfRank p L r) :
    AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank p r := by
  intro y
  obtain ⟨C, hC⟩ := H (p y)
  obtain ⟨x, hx⟩ := C.contains
  obtain ⟨a, ha, hay⟩ := Scheme.exists_preimage_of_isPullback C.square x y hx
  have hq : AffineSpace.SourceRank.BundleCycles.HasAffineSpaceSourceChartsOfRank
      (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase C.coefficient (C.coefficient × C.module)) r := by
    have h := Augmented.BasisSourceCharts.BundleCycles.symmetricAugmentedBasis_sourceCharts C.basis
    rw [Nat.card_fin, hC] at h
    exact h
  obtain ⟨U, i, ι, hι, j, hi, hj, haU, hs, hr⟩ := hq a
  let := hi
  let := hj
  refine ⟨U, i ≫ C.baseMap, ι, hι, j ≫ C.totalMap, inferInstance, inferInstance, ?_, ?_, hr⟩
  · obtain ⟨a', ha'⟩ := haU
    exact ⟨a', (congrArg C.totalMap ha').trans hay⟩
  · rw [← Category.assoc, hs, Category.assoc, C.square.w, Category.assoc]

end AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts.BundleCycles

namespace AlgebraicGeometry.Divisors.LineBundles.Free

/-! Genuine sheaf isomorphisms transport actual free infinity charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart.changeLineBundle {E X : Scheme.{0}} {p : E ⟶ X}
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {x : X} (C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L x)
    (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (e : M.sheaf ≅ L.sheaf) : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p M x where
  coefficient := C.coefficient
  module := C.module
  rank := C.rank
  basis := C.basis
  baseMap := C.baseMap
  totalMap := C.totalMap
  open_base := C.open_base
  open_total := C.open_total
  contains := C.contains
  square := C.square
  idealIso := LineBundle.PullbackIso.Cycles.lineBundlePullbackIso e C.totalMap ≪≫ C.idealIso

theorem InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank.changeLineBundle {E X : Scheme.{0}} {p : E ⟶ X}
    {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {r : ℕ} (H : InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank p L r)
    (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (e : M.sheaf ≅ L.sheaf) : InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank p M r := by
  intro x
  obtain ⟨C, hC⟩ := H x
  exact ⟨C.changeLineBundle M e, hC⟩

end AlgebraicGeometry.Divisors.LineBundles.Free

end

end OAI
