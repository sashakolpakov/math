import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi

/-! # Complex Assembly Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ComplexAssemblyRestriction

noncomputable section

/-! Restriction of assembled complexes preserves the original pointwise quasi-isomorphism criterion. -/

open _root_.CategoryTheory

universe u v u' v' w z

variable {T : Type u} [Category.{v} T] {S : Type u'} [Category.{v'} S]
  {V : Type w} [Category.{z} V] [Abelian V] (G : T ⥤ S) {α : Type*} (c : ComplexShape α)
  {F F' : S ⥤ HomologicalComplex V c} (a : F ⟶ F')

theorem quasiIso (ha : ∀ t, QuasiIso (a.app (G.obj t))) :
    QuasiIso ((((Functor.whiskeringLeft T S V).obj G).mapHomologicalComplex c).map
      (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map c a)) := by
  change QuasiIso (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map c (Functor.whiskerLeft G a))
  exact AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map_quasiIso c (Functor.whiskerLeft G a) ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ComplexAssemblyRestriction
