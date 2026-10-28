import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.AdjunctionChange

/-! # Invariant Object Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantObjectChange

noncomputable section

/-!
# Isomorphic objects with compatible Čech gluing have the same invariant
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  {L : C ⥤ D} {R : D ⥤ C} {P Q : D ⥤ E} {U V : E ⥤ D}
  (a : L ⊣ R) (b : P ⊣ U) (c : Q ⊣ V) (e : U ⋙ R ≅ V ⋙ R)
  {M N : D} (σ : P.obj M ⟶ Q.obj M) (τ : P.obj N ⟶ Q.obj N) (x : M ≅ N)
  (hx : P.map x.hom ≫ τ = σ ≫ Q.map x.hom)

open OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointCechInvariant

include hx in
/-- The gluing square transports through the projection adjunction. -/
theorem adjoint_square :
    b.homEquiv M (Q.obj M) σ ≫ U.map (Q.map x.hom) =
      x.hom ≫ b.homEquiv N (Q.obj N) τ := by
  have h := congrArg (b.homEquiv M (Q.obj N)) hx
  rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right] at h
  exact h.symm

include hx in
/-- A gluing-compatible object isomorphism carries the first invariant arrow to the first arrow. -/
theorem leftMap_square :
    AdjointCechInvariant.leftMap b e σ ≫ (V ⋙ R).map (Q.map x.hom) = R.map x.hom ≫ AdjointCechInvariant.leftMap b e τ := by
  rw [AdjunctionChange.leftMap_homEquiv, AdjunctionChange.leftMap_homEquiv]
  rw [Category.assoc, ← e.hom.naturality, ← Category.assoc]
  change (R.map (b.homEquiv M (Q.obj M) σ) ≫ R.map (U.map (Q.map x.hom))) ≫ _ = _
  rw [← R.map_comp, adjoint_square b σ τ x hx, R.map_comp, Category.assoc]

/-- The second invariant square is the naturality square of the other projection's unit. -/
theorem rightMap_square :
    AdjointCechInvariant.rightMap (R := R) c (M := M) ≫ (V ⋙ R).map (Q.map x.hom) =
      R.map x.hom ≫ AdjointCechInvariant.rightMap (R := R) c (M := N) := by
  change R.map (c.unit.app M) ≫ R.map (V.map (Q.map x.hom)) =
    R.map x.hom ≫ R.map (c.unit.app N)
  rw [← R.map_comp, ← R.map_comp]
  exact congrArg R.map (c.unit.naturality x.hom).symm

variable [HasEqualizers C]

/-- Compatible isomorphic original objects have canonically isomorphic actual invariants. -/
def invariantIso : AdjointCechInvariant.invariants b c e σ ≅ AdjointCechInvariant.invariants b c e τ :=
  HasLimit.isoOfNatIso (parallelPair.ext (R.mapIso x) ((V ⋙ R).mapIso (Q.mapIso x))
    (leftMap_square b e σ τ x hx) (rightMap_square (R := R) c x))

/-- The isomorphism retains the equalizer inclusion and the given original object isomorphism. -/
theorem invariantIso_hom_ι :
    (invariantIso b c e σ τ x hx).hom ≫ equalizer.ι (AdjointCechInvariant.leftMap b e τ) (AdjointCechInvariant.rightMap (R := R) c) =
      equalizer.ι (AdjointCechInvariant.leftMap b e σ) (AdjointCechInvariant.rightMap (R := R) c) ≫ R.map x.hom := by
  dsimp only [invariantIso, equalizer.ι]
  exact HasLimit.isoOfNatIso_hom_π _ _

/-- The canonical pullback comparison transports by the specified object isomorphism. -/
theorem comparison_fac :
    L.map (invariantIso b c e σ τ x hx).hom ≫ AdjointCechInvariant.comparison a b c e τ =
      AdjointCechInvariant.comparison a b c e σ ≫ x.hom := by
  apply (a.homEquiv _ _).injective
  rw [AdjointCechInvariant.homEquiv_map_comparison, a.homEquiv_naturality_right, AdjointCechInvariant.comparison_homEquiv]
  exact invariantIso_hom_ι b c e σ τ x hx

include hx in
/-- Effectivity is preserved by an isomorphism that retains the supplied gluing. -/
theorem comparison_isIso_iff :
    IsIso (AdjointCechInvariant.comparison a b c e σ) ↔ IsIso (AdjointCechInvariant.comparison a b c e τ) := by
  calc
    IsIso (AdjointCechInvariant.comparison a b c e σ) ↔ IsIso (AdjointCechInvariant.comparison a b c e σ ≫ x.hom) :=
      (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso (L.map (invariantIso b c e σ τ x hx).hom ≫ AdjointCechInvariant.comparison a b c e τ) := by
      rw [comparison_fac a b c e σ τ x hx]
    _ ↔ IsIso (AdjointCechInvariant.comparison a b c e τ) := isIso_comp_left_iff _ _

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.InvariantObjectChange
