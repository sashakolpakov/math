import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Bundle
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso

/-! # Projective Infinity Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart.BundleCycles

noncomputable section

/-! Actual finite free projective charts with their infinity ideal
identifications. The data consists entirely of schemes, bases, cartesian
squares and sheaf isomorphisms. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

structure FreeProjectiveInfinityChart {E X : Scheme.{0}} (p : E ⟶ X)
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) (x : X) where
  coefficient : CommRingCat.{0}
  module : ModuleCat.{0} coefficient
  rank : ℕ
  basis : Module.Basis (Fin rank) coefficient module
  baseMap : Spec coefficient ⟶ X
  totalMap : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme coefficient (coefficient × module) ⟶ E
  open_base : IsOpenImmersion baseMap
  open_total : IsOpenImmersion totalMap
  contains : x ∈ Set.range baseMap
  square : IsPullback (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase coefficient (coefficient × module)) totalMap baseMap p
  idealIso : (L.pullback totalMap).sheaf ≅ (SymmetricInfinity.Bundle.Cycles.symmetricInfinityIdealLineBundle coefficient module).sheaf

attribute [instance] FreeProjectiveInfinityChart.open_base FreeProjectiveInfinityChart.open_total

def HasFreeProjectiveInfinityCharts {E X : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E) : Prop :=
  ∀ x : X, Nonempty (FreeProjectiveInfinityChart p L x)

def FreeProjectiveInfinityChart.compOpen {E X E' X' : Scheme.{0}}
    {p : E ⟶ X} {L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E} {x : X} (C : FreeProjectiveInfinityChart p L x)
    (q : E' ⟶ X') (i : X ⟶ X') (j : E ⟶ E') [IsOpenImmersion i] [IsOpenImmersion j]
    (hs : IsPullback p j i q) (M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E') (e : (M.pullback j).sheaf ≅ L.sheaf) :
    FreeProjectiveInfinityChart q M (i x) where
  coefficient := C.coefficient
  module := C.module
  rank := C.rank
  basis := C.basis
  baseMap := C.baseMap ≫ i
  totalMap := C.totalMap ≫ j
  open_base := inferInstance
  open_total := inferInstance
  contains := by
    obtain ⟨y, hy⟩ := C.contains
    exact ⟨y, congrArg i hy⟩
  square := C.square.paste_vert hs
  idealIso := (LineBundle.PullbackIso.Cycles.lineBundlePullbackCompIso M C.totalMap j).symm ≪≫
    LineBundle.PullbackIso.Cycles.lineBundlePullbackIso e C.totalMap ≪≫ C.idealIso

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ProjectiveInfinityChart.BundleCycles
