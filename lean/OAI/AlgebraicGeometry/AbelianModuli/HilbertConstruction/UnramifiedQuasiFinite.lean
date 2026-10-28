import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Unramified Quasi Finite -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite

noncomputable section

/-! An unramified morphism is locally quasi-finite. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem locallyQuasiFinite_of_unramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f where
  quasiFinite_appLE {U} hU {V} hV e := by
    have hf := f.formallyUnramified_appLE hU hV e
    have ht := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedQuasiFinite
