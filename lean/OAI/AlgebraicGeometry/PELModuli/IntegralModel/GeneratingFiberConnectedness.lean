import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Words
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Generating Fiber Connectedness -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness

noncomputable section

/-! A surjective finite difference word forces geometric connectedness of
its target. This applies to every specialization of the coefficient family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem geometricallyConnected_of_surjective_map {S : Scheme} {X Y : Over S}
    [GeometricallyConnected X.hom] (f : X ⟶ Y) [Surjective f.left] :
    GeometricallyConnected Y.hom := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ t ↦ ?_⟩
  have : ConnectedSpace (pullback X.hom t : Scheme) :=
    GeometricallyConnected.geometrically_connectedSpace t _ _ (.of_hasPullback _ _)
  have : ConnectedSpace ((Over.pullback t).obj X).left :=
    inferInstanceAs (ConnectedSpace (pullback X.hom t : Scheme))
  have hf : Surjective ((Over.pullback t).map f).left := MorphismProperty.of_isPullback
    (Specialization.base_change_square t f) (inferInstanceAs (Surjective f.left))
  exact hf.surj.connectedSpace ((Over.pullback t).map f).left.continuous

theorem geometricallyConnected_tensor {S : Scheme} (X Y : Over S)
    [GeometricallyConnected X.hom] [GeometricallyConnected Y.hom]
    [UniversallyOpen X.hom] [UniversallyOpen Y.hom] :
    GeometricallyConnected (X ⊗ Y).hom := by
  change GeometricallyConnected (pullback.fst X.hom Y.hom ≫ X.hom)
  exact GeometricallyConnected.comp _ _

namespace DifferenceWords

theorem domain_geometricallyConnected {S : Scheme} (X : Over S)
    [GeometricallyConnected X.hom] [Smooth X.hom] (n : ℕ) :
    GeometricallyConnected (Words.DifferenceWords.domain X n).hom := by
  induction n with
  | zero =>
    change GeometricallyConnected (𝟙 S)
    refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ t ↦ ?_⟩
    have : IsIso (pullback.snd (𝟙 S) t) := inferInstance
    exact (pullback.snd (𝟙 S) t).homeomorph.connectedSpace_iff.mpr inferInstance
  | succ n ih =>
    have : GeometricallyConnected (X ⊗ X).hom := geometricallyConnected_tensor X X
    have : Smooth (X ⊗ X).hom := by
      change Smooth (pullback.fst X.hom X.hom ≫ X.hom)
      infer_instance
    exact geometricallyConnected_tensor (Words.DifferenceWords.domain X n) (X ⊗ X)

/-- Generation of an arithmetic fiber supplies the connectedness needed
to regard the specialized smooth proper group as an abelian variety. -/
theorem target_geometricallyConnected {S : Scheme} {X A : Over S}
    [GeometricallyConnected X.hom] [Smooth X.hom] [GrpObj A]
    (a : X ⟶ A) (n : ℕ) [Surjective (Words.DifferenceWords.map a n).left] : GeometricallyConnected A.hom := by
  have : GeometricallyConnected (Words.DifferenceWords.domain X n).hom := domain_geometricallyConnected X n
  exact geometricallyConnected_of_surjective_map (Words.DifferenceWords.map a n)

end DifferenceWords

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.GeneratingFiberConnectedness
