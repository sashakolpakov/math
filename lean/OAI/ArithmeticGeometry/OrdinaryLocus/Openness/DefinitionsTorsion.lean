import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.Topology.KrullDimension
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.ZMod.Basic

/-! # Definitions Torsion -/

namespace OAI

noncomputable section

namespace ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion

/-! Definitions used in the Openness statement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

/-- Spec of an algebraic closure of κ(s), as an S-scheme. -/
def geometricPoint (S : Scheme) (s : S) : Over S :=
  Over.mk
    (Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField s)
        (AlgebraicClosure (S.residueField s)))) ≫
      S.fromSpecResidueField s)

/-- A fiber of dimension g is ordinary when it has p^g geometric
p-torsion points. Here x^p = 1 means [p]x = 0 additively. -/
def IsOrdinaryAt (p : ℕ) {S : Scheme}
    (A : Over S) [GrpObj A] (s : S) : Prop :=
  ∃ g : ℕ,
    topologicalKrullDim (A.hom.fiber s) = (g : WithBot ℕ∞) ∧
    Nat.card {x : geometricPoint S s ⟶ A // x ^ p = 1} = p ^ g

end ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion

namespace ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
section

/-!
Scheme-theoretic torsion and its geometric points for Openness.
Only the definitions in `Statements.Openness` are used; its theorem stub is not used.
-/

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion (geometricPoint IsOrdinaryAt)

variable {S : Scheme} (A : Over S) [GrpObj A]

/-- The kernel of multiplication by `n`, represented as an equalizer over S. -/
def torsionScheme (n : ℕ) : Over S :=
  equalizer ((𝟙 A) ^ n) (1 : A ⟶ A)

/-- The inclusion of the scheme-theoretic n-torsion. -/
def torsionInclusion (n : ℕ) : torsionScheme A n ⟶ A :=
  equalizer.ι ((𝟙 A) ^ n) (1 : A ⟶ A)

/-- The representing property identifies points with elements killed by n. -/
def torsionPointsEquiv (n : ℕ) (T : Over S) :
    (T ⟶ torsionScheme A n) ≃ {x : T ⟶ A // x ^ n = 1} where
  toFun f := ⟨f ≫ torsionInclusion A n, by
    have h : (torsionInclusion A n) ^ n = 1 := by
      convert! (show (equalizer.ι ((𝟙 A) ^ n) (1 : A ⟶ A)) ^ n = 1 from
        (by simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using
          (equalizer.condition ((𝟙 A) ^ n) (1 : A ⟶ A))))
    rw [← MonObj.comp_pow, h, MonObj.comp_one]⟩
  invFun x := equalizer.lift x.val (by
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using x.prop)
  left_inv f := by
    apply equalizer.hom_ext
    exact equalizer.lift_ι _ _
  right_inv x := by
    apply Subtype.ext
    exact equalizer.lift_ι _ _

instance torsionInclusion_isClosedImmersion (n : ℕ) [IsSeparated A.hom] :
    IsClosedImmersion (torsionInclusion A n).left := by
  exact isClosedImmersion_equalizer_ι_left ((𝟙 A) ^ n) (1 : A ⟶ A)

instance torsionScheme_isProper (n : ℕ) [IsProper A.hom] :
    IsProper (torsionScheme A n).hom := by
  rw [← (torsionInclusion A n).w]
  infer_instance

/-- The torsion count in the specification is the geometric-point count
of the actual torsion scheme. -/
theorem geometric_torsion_card (n : ℕ) (s : S) :
    Nat.card (geometricPoint S s ⟶ torsionScheme A n) =
      Nat.card {x : geometricPoint S s ⟶ A // x ^ n = 1} :=
  Nat.card_congr (torsionPointsEquiv A n (geometricPoint S s))

theorem isOrdinaryAt_iff_torsionScheme (p : ℕ) (s : S) :
    IsOrdinaryAt p A s ↔
      ∃ g : ℕ,
        topologicalKrullDim (A.hom.fiber s) = (g : WithBot ℕ∞) ∧
        Nat.card (geometricPoint S s ⟶ torsionScheme A p) = p ^ g := by
  simp only [IsOrdinaryAt, geometric_torsion_card]

/-- Ordinarity in the specification forces the geometric torsion set
to be finite; `Nat.card` cannot certify an infinite set as ordinary. -/
theorem finite_geometric_torsion_of_isOrdinaryAt
    (p : ℕ) [Fact p.Prime] (s : S) (hs : IsOrdinaryAt p A s) :
    Finite (geometricPoint S s ⟶ torsionScheme A p) := by
  obtain ⟨g, _, hg⟩ := (isOrdinaryAt_iff_torsionScheme A p s).mp hs
  apply Nat.finite_of_card_ne_zero
  rw [hg]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

end

/-! Relating geometric points in Openness to the actual geometric fiber scheme. -/

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion (geometricPoint IsOrdinaryAt)

variable {S : Scheme} (T : Over S) (s : S)

/-- The geometric fiber over the algebraic closure used in the specification. -/
abbrev geometricFiberScheme : Scheme :=
  pullback T.hom (geometricPoint S s).hom

/-- Its structure map to the algebraically closed residue field. -/
abbrev geometricFiberMap : geometricFiberScheme T s ⟶ (geometricPoint S s).left :=
  pullback.snd T.hom (geometricPoint S s).hom

instance geometricFiberMap_locallyOfFiniteType [LocallyOfFiniteType T.hom] :
    LocallyOfFiniteType (geometricFiberMap T s) := by
  unfold geometricFiberMap
  infer_instance

/-- A geometric point over S is equivalently a point of the geometric fiber
over its algebraically closed base field. -/
def geometricFiberPointEquiv :
    (geometricPoint S s ⟶ T) ≃
      {p : (geometricPoint S s).left ⟶ geometricFiberScheme T s //
        p ≫ geometricFiberMap T s = 𝟙 _} where
  toFun f := ⟨pullback.lift f.left (𝟙 _) (by simp), by
    exact pullback.lift_snd _ _ _⟩
  invFun p := Over.homMk (p.val ≫ pullback.fst T.hom (geometricPoint S s).hom) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, p.prop,
      Category.id_comp])
  left_inv f := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.prop.symm

/-- The geometric points in Openness correspond to closed points of the geometric fiber. -/
def geometricClosedPointEquiv [LocallyOfFiniteType T.hom] :
    (geometricPoint S s ⟶ T) ≃ closedPoints (geometricFiberScheme T s) := by
  let f : geometricFiberScheme T s ⟶
      Spec (.of (AlgebraicClosure (S.residueField s))) := geometricFiberMap T s
  have : LocallyOfFiniteType f := by
    exact geometricFiberMap_locallyOfFiniteType T s
  exact (geometricFiberPointEquiv T s).trans (pointEquivClosedPoint f)

/-- Over an algebraically closed field, a finite-type scheme with finitely
many rational points has finitely many underlying scheme points. -/
theorem finite_geometricFiber_of_finite_points [LocallyOfFiniteType T.hom]
    [Finite (geometricPoint S s ⟶ T)] : Finite (geometricFiberScheme T s) := by
  have : Finite (closedPoints (geometricFiberScheme T s)) :=
    Finite.of_equiv _ (geometricClosedPointEquiv T s)
  have : JacobsonSpace (geometricPoint S s).left := by
    change JacobsonSpace (Spec (.of (AlgebraicClosure (S.residueField s))))
    infer_instance
  have : JacobsonSpace (geometricFiberScheme T s) :=
    LocallyOfFiniteType.jacobsonSpace (geometricFiberMap T s)
  have hfin : (closedPoints (geometricFiberScheme T s)).Finite := Set.toFinite _
  have : DiscreteTopology (geometricFiberScheme T s) :=
    JacobsonSpace.discreteTopology hfin
  have : (Set.univ : Set (geometricFiberScheme T s)).Finite := by
    simpa only [closedPoints_eq_univ] using hfin
  exact Set.finite_univ_iff.mp this

theorem geometricPoint_range : Set.range (geometricPoint S s).hom = {s} := by
  ext t
  constructor
  · rintro ⟨x, rfl⟩
    exact S.fromSpecResidueField_apply s _
  · intro ht
    have ht' : t = s := ht
    subst t
    refine ⟨IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s)), ?_⟩
    exact S.fromSpecResidueField_apply s _

/-- Finitely many geometric points imply a finite set-theoretic fiber. -/
theorem finite_preimage_of_finite_geometric_points [LocallyOfFiniteType T.hom]
    [Finite (geometricPoint S s ⟶ T)] : (T.hom ⁻¹' {s}).Finite := by
  have : Finite (geometricFiberScheme T s) :=
    finite_geometricFiber_of_finite_points T s
  have h := Set.finite_range (pullback.fst T.hom (geometricPoint S s).hom)
  rwa [Scheme.Pullback.range_fst, geometricPoint_range] at h

/-- Properness turns a finite geometric fiber into finiteness over an open neighborhood. -/
theorem exists_finite_neighborhood_of_finite_geometric_points [IsProper T.hom]
    [Finite (geometricPoint S s ⟶ T)] :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite (T.hom ∣_ U) := by
  exact exists_isFinite_morphismRestrict_of_finite_preimage_singleton T.hom s
    (finite_preimage_of_finite_geometric_points T s)

/-- At an ordinary point, the actual p-torsion scheme is finite over
some open neighborhood. No openness of ordinarity is used here. -/
theorem exists_finite_torsion_neighborhood
    (A : Over S) [GrpObj A] [IsProper A.hom]
    (p : ℕ) [Fact p.Prime] (hs : IsOrdinaryAt p A s) :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite ((torsionScheme A p).hom ∣_ U) := by
  have : Finite (geometricPoint S s ⟶ torsionScheme A p) :=
    finite_geometric_torsion_of_isOrdinaryAt A p s hs
  exact exists_finite_neighborhood_of_finite_geometric_points (torsionScheme A p) s

end ArithmeticGeometry.OrdinaryLocus.Openness.DefinitionsTorsion.Construction

end

end OAI
