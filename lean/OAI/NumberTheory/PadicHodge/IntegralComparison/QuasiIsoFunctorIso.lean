import Mathlib.Algebra.Homology.QuasiIso

/-! # Quasi Iso Functor Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso

/-! A natural isomorphism of complex-valued functors preserves quasi-isomorphisms of their images. -/

open _root_.CategoryTheory

universe u v u' v'

theorem transport {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] {α : Type*} {c : ComplexShape α}
    (F G : C ⥤ HomologicalComplex D c) (e : F ≅ G) {X Y : C} (f : X ⟶ Y)
    [QuasiIso (F.map f)] : QuasiIso (G.map f) :=
  quasiIso_of_arrow_mk_iso (F.map f) (G.map f)
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)

end OAI.NumberTheory.PadicHodge.IntegralComparison.QuasiIsoFunctorIso
