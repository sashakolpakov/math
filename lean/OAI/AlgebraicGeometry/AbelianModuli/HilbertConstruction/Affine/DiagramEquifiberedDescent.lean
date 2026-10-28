import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientSquarePullbackDescent
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
import Mathlib.Basic.Finite.Sigma

/-! # Diagram Equifibered Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.DiagramEquifiberedDescent

noncomputable section

/-! A finite affine diagram map becomes equifibered over finite coefficients when its original base change is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

theorem exists_affine_diagram_equifibered_extension
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {J : Type v} [Category.{w} J] [Quiver.IsThin J] [Finite J]
    (F G : J ⥤ Over (Spec (.of C)))
    [∀ i, IsAffine (F.obj i).left] [∀ i, IsAffine (G.obj i).left]
    [∀ i, Smooth (F.obj i).hom]
    [∀ {i j} (h : i ⟶ j), IsOpenImmersion (G.map h).left]
    (q : F ⟶ G)
    [∀ i, IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map (q.app i))]
    (E : Subalgebra C R) (hE : E.FG) :
    ∃ D : Subalgebra C R, E ≤ D ∧ D.FG ∧
      (Functor.whiskerRight q (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C D))))).Equifibered := by
  let I := Σ i j : J, i ⟶ j
  have : Finite I := inferInstanceAs (Finite (Σ i j : J, i ⟶ j))
  obtain ⟨D, hED, hD, hd⟩ := AmbientSquarePullbackDescent.exists_common_ambient_square_pullbacks
    (fun k : I => F.obj k.1) (fun k : I => F.obj k.2.1)
    (fun k : I => G.obj k.1) (fun k : I => G.obj k.2.1)
    (fun k => F.map k.2.2) (fun k => q.app k.1) (fun k => q.app k.2.1)
    (fun k => G.map k.2.2) (fun k => q.naturality k.2.2) E hE
  exact ⟨D, hED, hD, fun i j h => hd ⟨i, j, h⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.DiagramEquifiberedDescent
