import OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Cartier Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierRank.Construction

noncomputable section

/-!
Cartier duality preserves the actual finite-flat rank over a field.
The comparison uses the constructed dual Hopf algebra and the unique
isomorphism of character representatives.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.CartierDuality.PolarizedTorsion.Construction OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation.Construction

universe u

theorem groupScheme_finrank_of_hopfIso
    {k : Type u} [Field k] (R : CommHopfAlgCat k) [Module.Finite k R]
    (G : Grp (Over (Spec (.of k)))) [IsFinite G.X.hom] [Flat G.X.hom]
    (e : (hopfSpec (.of k)).obj (.op R) ≅ G) (s : Spec (.of k)) :
    G.X.hom.finrank s = Module.finrank k R := by
  let i : ((hopfSpec (.of k)).obj (.op R)).X ≅ G.X := (Grp.forget _).mapIso e
  have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
  have h : ((hopfSpec (.of k)).obj (.op R)).X.hom.finrank s = Module.finrank k R := by
    change (Spec.map (CommRingCat.ofHom (algebraMap k R))).finrank s = _
    have hs := Scheme.Hom.finrank_SpecMap_algebraMap k R (show PrimeSpectrum k from s)
    rw [Module.rankAtStalk_eq_finrank_of_free] at hs
    exact hs
  rw [← i.hom.w, Scheme.Hom.finrank_comp_left_of_isIso] at h
  exact h

theorem cartierGroupRepresentation_finrank
    {k : Type u} [Field k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom]
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) G) (s : Spec (.of k)) :
    C.dual.X.hom.finrank s = G.X.hom.finrank s := by
  obtain ⟨R, hf, hc, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hf
  have : Coalgebra.IsCocomm k R := hc
  have : IsFinite C.dual.X.hom := C.finite
  have : Flat C.dual.X.hom := C.flat
  let D := CartierDuality.PolarizedTorsion.Construction.affineCartierGroupRepresentation k R
  let j : C.dual.X ≅ D.dual.X := (Grp.forget _).mapIso (C.dualMapIso D e)
  have : IsIso j.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom))
  have : IsFinite D.dual.X.hom := D.finite
  have : Flat D.dual.X.hom := D.flat
  have hr : D.dual.X.hom.finrank s = Module.finrank k (CartierDuality.DualAlgebra.Construction.DualCoordinate k R) := by
    change (Spec.map (CommRingCat.ofHom (algebraMap k (CartierDuality.DualAlgebra.Construction.DualCoordinate k R)))).finrank s = _
    have hs := Scheme.Hom.finrank_SpecMap_algebraMap k (CartierDuality.DualAlgebra.Construction.DualCoordinate k R)
      (show PrimeSpectrum k from s)
    rw [Module.rankAtStalk_eq_finrank_of_free] at hs
    exact hs
  calc
    C.dual.X.hom.finrank s = D.dual.X.hom.finrank s := by
      rw [← j.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
    _ = Module.finrank k (CartierDuality.DualAlgebra.Construction.DualCoordinate k R) := hr
    _ = Module.finrank k R :=
      (CartierDuality.DualAlgebra.Construction.dualCoordinateLinearEquiv k R).finrank_eq.trans (Subspace.dual_finrank_eq ..)
    _ = G.X.hom.finrank s := (groupScheme_finrank_of_hopfIso R G e s).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierRank.Construction
