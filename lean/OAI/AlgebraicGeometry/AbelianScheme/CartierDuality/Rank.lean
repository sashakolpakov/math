import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.AffineSheafIso
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FiniteLocallyFreeCoordinates
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Rank -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank

noncomputable section

/-!
# CartierDuality: actual Cartier duality preserves finite-flat rank over fields
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation.Construction
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.Schemes

/-- An isomorphism over the base preserves the actual finite-flat rank. -/
theorem overIso_finrank {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) [IsFinite Y.hom] [Flat Y.hom] (s : S) :
    X.hom.finrank s = Y.hom.finrank s := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← e.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]

/-- The scheme rank of a finite algebra over a field is its ordinary vector-space dimension. -/
theorem spec_finrank_field (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Module.Finite k R]
    (s : Spec (.of k)) :
    (Spec.map (CommRingCat.ofHom (algebraMap k R))).finrank s = Module.finrank k R := by
  have h := Scheme.Hom.finrank_SpecMap_algebraMap k R (show PrimeSpectrum k from s)
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  exact h

variable (k : Type u) [Field k] (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsFinite G.X.hom] [Flat G.X.hom]
    (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) G)

/-- The actual Cartier representative has the same scheme-theoretic order as its original group. -/
theorem characterRepresentative_finrank (s : Spec (.of k)) :
    C.dual.X.hom.finrank s = G.X.hom.finrank s := by
  obtain ⟨R, hR, hc, ⟨e⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  have : Coalgebra.IsCocomm k R := hc
  let Y : Over (Spec (.of k)) := (Spec (.of (DualAlgebra.Construction.DualCoordinate k R))).asOver (Spec (.of k))
  have hY : IsFinite Y.hom ∧ Flat Y.hom ∧ LocallyOfFinitePresentation Y.hom :=
    (FiniteLocallyFreeCoordinates.Construction.finiteLocallyFree_spec_iff k (DualAlgebra.Construction.DualCoordinate k R)).mpr ⟨inferInstance, inferInstance⟩
  have : IsFinite Y.hom := hY.1
  have : Flat Y.hom := hY.2.1
  let j : CharacterFunctor.Construction.Schemes.pointSheaf (Spec (.of k)) Y ≅ CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) ((hopfSpec (.of k)).obj (.op R)) :=
    @asIso _ _ _ _ (CharacterMap.Construction.affineCartierCharacterSheafMap k R) (AffineSheafIso.Construction.affineCartierCharacterSheafMap_isIso k R)
  let d : C.dual.X ≅ Y := uliftYoneda.{u + 1}.preimageIso
    ((sheafToPresheaf _ _).mapIso (C.sheafIso ≪≫ CharacterFunctor.Construction.Schemes.characterSheafIso e ≪≫ j.symm))
  let i : ((hopfSpec (.of k)).obj (.op R)).X ≅ G.X := (Grp.forget _).mapIso e
  calc
    C.dual.X.hom.finrank s = Y.hom.finrank s := overIso_finrank d s
    _ = Module.finrank k (DualAlgebra.Construction.DualCoordinate k R) := spec_finrank_field k (DualAlgebra.Construction.DualCoordinate k R) s
    _ = Module.finrank k (Module.Dual k R) := (DualAlgebra.Construction.dualCoordinateLinearEquiv k R).finrank_eq
    _ = Module.finrank k R := Subspace.dual_finrank_eq
    _ = (((hopfSpec (.of k)).obj (.op R)).X).hom.finrank s := (spec_finrank_field k R s).symm
    _ = G.X.hom.finrank s := overIso_finrank i s

end Construction.Schemes

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Rank
