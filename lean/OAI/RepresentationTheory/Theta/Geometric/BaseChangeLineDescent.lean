import OAI.RepresentationTheory.Theta.Geometric.BaseChangeFunctionDescent
import OAI.RepresentationTheory.Theta.Geometric.Affine.FunctionLineDescent
import OAI.RepresentationTheory.Theta.Geometric.Affine.Dominance

/-! # Base Change Line Descent -/

namespace OAI.RepresentationTheory.Theta.Geometric.BaseChangeLineDescent

noncomputable section

/-! Compatible native line-bundle isomorphisms descend over a flat
family along the injected parameter algebra equalizer. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem flat_baseChange_lineIso_descent
    {A R P : Type} [CommRing A] [CommRing R] [CommRing P] [Algebra A R] [Algebra A P]
    (hi : Function.Injective (algebraMap A R)) (f g : R →ₐ[A] P)
    (he : Function.Exact (Algebra.linearMap A R) (f.toLinearMap - g.toLinearMap))
    {Y Z : Scheme} (h : Y ⟶ Spec (.of A)) [Flat h] (u : Z ⟶ Y) (v : Z ⟶ Spec (.of R))
    (H : IsPullback u v h (Spec.map (CommRingCat.ofHom (algebraMap A R))))
    {M N : Y.Modules} (hM : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle M) (hN : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.IsLineBundle N)
    (e : (Scheme.Modules.pullback u).obj M ≅ (Scheme.Modules.pullback u).obj N)
    (heq : AlgebraicGeometry.Isogenies.NeighborCounting.FramedDescent.CompatibleHom u e.hom) :
    ∃! d : M ≅ N, (Scheme.Modules.pullback u).mapIso d = e := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap A R))) :=
    Affine.Dominance.specMap_schemeTheoreticallyDominant _ hi
  have : IsSchemeTheoreticallyDominant u := IsSchemeTheoreticallyDominant.of_isPullback H.flip
  have : QuasiCompact u := MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip
    (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap A R)))))
  exact Affine.FunctionLineDescent.existsUnique_lineIso_of_affine_function_descent u
    (BaseChangeFunctionDescent.flat_isPullback_affineFunctionDescent hi f g he h u v H) hM hN e heq

end

end OAI.RepresentationTheory.Theta.Geometric.BaseChangeLineDescent
