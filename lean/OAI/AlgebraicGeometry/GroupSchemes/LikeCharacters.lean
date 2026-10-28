import OAI.AlgebraicGeometry.GroupSchemes.DualPoints
import OAI.AlgebraicGeometry.GroupSchemes.EtaleCyclic

/-! # Like Characters -/

namespace OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters

noncomputable section

/-! Cartier-dual rational points as a basis of grouplike coordinate characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

namespace FiniteEtale

universe u
variable (k A : Type u) [Field k] [CommRing A] [HopfAlgebra k A]
  [Coalgebra.IsCocomm k A] [Module.Finite k A]

local instance : CommRing (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convCommRing
local instance : Algebra k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) := LinearMap.convAlgebra

/-- Dual rational points are precisely grouplike elements, compatibly with multiplication. -/
def dualPointsEquivGroupLike : WithConv (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A →ₐ[k] k) ≃* GroupLike k A where
  toEquiv := (WithConv.equiv _).trans
    ((AbelianScheme.CartierDuality.DualAlgebra.Construction.groupLikeDualEquivAlgHom k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A)).symm.trans
      (AbelianScheme.CartierDuality.DualAlgebra.Construction.groupLikeCongr k (AbelianScheme.CartierDuality.DualAlgebra.Construction.dualCoordinateBidualBialgEquiv k A).toCoalgEquiv).symm)
  map_mul' f g := by
    apply GroupLike.val_injective
    exact (DualPoints.FiniteEtale.pointElement k A).map_mul f g

/-- The same character equivalence for the actual Cartier-dual group scheme. -/
def dualOfHopfGroupLikeEquiv :
    (FiniteEtale.FiniteCommGroupScheme.dualOfHopf (k := k) A).rationalPoints ≃* GroupLike k A :=
  (@Spec.mapMulEquiv k (AbelianScheme.CartierDuality.DualAlgebra.Construction.DualCoordinate k A) k _ _ _ inferInstance _).symm.trans
    (dualPointsEquivGroupLike k A)

/-- A bialgebra map carries grouplike characters to grouplike characters. -/
def groupLikeMap {B : Type u} [CommRing B] [HopfAlgebra k B]
    (q : A →ₐc[k] B) : GroupLike k A →* GroupLike k B where
  toFun x := ⟨q x.val, x.isGroupLikeElem_val.map q⟩
  map_one' := by apply GroupLike.val_injective; exact q.map_one
  map_mul' x y := by apply GroupLike.val_injective; exact q.map_mul x.val y.val

omit [Coalgebra.IsCocomm k A] [Module.Finite k A] in
/-- If grouplike elements span the source, a surjective bialgebra map is surjective on them. -/
theorem groupLikeMap_surjective {B : Type u} [CommRing B] [HopfAlgebra k B]
    (q : A →ₐc[k] B) (hq : Function.Surjective q)
    (hspan : Submodule.span k (Set.range (GroupLike.val (R := k) (A := A))) = ⊤) :
    Function.Surjective (groupLikeMap k A q) := by
  have hspanB : Submodule.span k (Set.range (fun x : GroupLike k A => q x.val)) = ⊤ := by
    change Submodule.span k (Set.range (q.toLinearMap ∘ GroupLike.val)) = ⊤
    rw [Set.range_comp, Submodule.span_image, hspan, Submodule.map_top,
      LinearMap.range_eq_top]
    exact hq
  intro x
  by_contra hx
  have hsubset : Set.range (fun a : GroupLike k A => q a.val) ⊆
      GroupLike.val '' ({x}ᶜ : Set (GroupLike k B)) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨groupLikeMap k A q a, ?_, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (not_exists.mp hx a)
  have hmem : x.val ∈ Submodule.span k (Set.range (fun a : GroupLike k A => q a.val)) := by
    rw [hspanB]
    trivial
  exact (linearIndep_groupLikeVal (R := k) (A := B)).notMem_span x
    (Submodule.span_mono hsubset hmem)

end FiniteEtale

namespace FiniteEtale.FiniteCommGroupScheme

universe u
variable {k : Type u} [Field k]

/-- The group of grouplike coordinate characters of the given geometric group. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterGroup (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) : CommGrpCat.{u} := by
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  let := G.coordinateHopf
  exact CommGrpCat.of (GroupLike k G.algebra)

/-- Actual Cartier-dual rational points are the coordinate characters. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.dualPointsCharacterEquiv (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    G.cartierDual.rationalPoints ≃* G.characterGroup :=
  @dualOfHopfGroupLikeEquiv k G.algebra _ _
    G.coordinateHopf G.coordinateHopf_cocomm G.finite

instance _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterGroup_finite (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) : Finite G.characterGroup :=
  Finite.of_equiv G.cartierDual.rationalPoints G.dualPointsCharacterEquiv.toEquiv

/-- The underlying coordinate element of a character. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterValue (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) : G.characterGroup →* G.algebra := by
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  let := G.coordinateHopf
  exact GroupLike.valMonoidHom k G.algebra

/-- With split Cartier dual, the character count equals the coordinate dimension. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterGroup_card [IsAlgClosed k] (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.cartierDual.algebra] :
    Nat.card G.characterGroup = Module.finrank k G.algebra :=
  (Nat.card_congr G.dualPointsCharacterEquiv.toEquiv).symm.trans
    (G.cartierDual.rationalPoints_card.trans G.cartierDual_rank)

/-- The coordinate characters are linearly independent. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterValue_linearIndependent (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k) :
    LinearIndependent k G.characterValue := by
  let : Algebra k G.algebra := G.coordinateHopf.toAlgebra
  let := G.coordinateHopf
  exact linearIndep_groupLikeVal (R := k) (A := G.algebra)

/-- With split Cartier dual, coordinate characters form a basis. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterValue_span [IsAlgClosed k] (G : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k)
    [Algebra.IsFiniteSplit k G.cartierDual.algebra] :
    Submodule.span k (Set.range G.characterValue) = ⊤ := by
  have : Fintype G.characterGroup := Fintype.ofFinite _
  apply G.characterValue_linearIndependent.span_eq_top_of_card_eq_finrank'
  simpa only [Nat.card_eq_fintype_card] using G.characterGroup_card

/-- Restriction of characters along an actual geometric group morphism. -/
def _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterMap {G H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k} (f : G.scheme ⟶ H.scheme) [IsMonHom f] :
    H.characterGroup →* G.characterGroup :=
  @groupLikeMap k H.algebra _ _ H.coordinateHopf
    G.algebra _ G.coordinateHopf (FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap f)

/-- Restriction along a closed immersion is onto when the source dual is split. -/
theorem _root_.OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale.FiniteCommGroupScheme.characterMap_surjective [IsAlgClosed k] {G H : GroupSchemes.FiniteEtale.FiniteCommGroupScheme k}
    [Algebra.IsFiniteSplit k H.cartierDual.algebra]
    (f : G.scheme ⟶ H.scheme) [IsMonHom f] [IsClosedImmersion f.left] :
    Function.Surjective (FiniteEtale.FiniteCommGroupScheme.characterMap f) :=
  @groupLikeMap_surjective k H.algebra _ _ H.coordinateHopf
    G.algebra _ G.coordinateHopf (FiniteEtale.FiniteCommGroupScheme.coordinateBialgMap f)
    (FiniteEtale.FiniteCommGroupScheme.coordinateMap_surjective f) H.characterValue_span

end FiniteEtale.FiniteCommGroupScheme

end

end OAI.AlgebraicGeometry.GroupSchemes.LikeCharacters
