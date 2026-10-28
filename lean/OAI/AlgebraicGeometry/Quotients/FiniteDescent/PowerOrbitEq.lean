import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AbelianQuotient
import Mathlib.GroupTheory.OrderOfElement

/-! # Power Orbit Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq.Construction.PowerOrbit

/-!
# Collapsing finite subgroup orbits by multiplication

Every orbit on underlying points is killed by one positive multiplication
map. This only uses finiteness of the subgroup: geometric points of the
subgroup form finite abstract groups, and an orbit has finitely many points.
Thus finiteness of positive multiplication maps supplies the affine-orbit
neighborhoods required by the relative quotient construction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

noncomputable def fieldPointPullbackEquiv {S : Scheme.{u}} (H : Over S)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    (Over.mk a ⟶ H) ≃ {p : Spec (.of K) ⟶ pullback H.hom a //
      p ≫ pullback.snd H.hom a = 𝟙 _} where
  toFun f := ⟨pullback.lift f.left (𝟙 _) (by simp), pullback.lift_snd _ _ _⟩
  invFun p := Over.homMk (p.val ≫ pullback.fst H.hom a) (by
    change (p.val ≫ pullback.fst H.hom a) ≫ H.hom = a
    rw [Category.assoc, pullback.condition, ← Category.assoc, p.prop, Category.id_comp])
  left_inv f := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  right_inv p := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans p.prop.symm

theorem finite_fieldPoints {S : Scheme.{u}} (H : Over S) [IsFinite H.hom]
    {K : Type u} [Field K] [IsAlgClosed K] (a : Spec (.of K) ⟶ S) :
    Finite (Over.mk a ⟶ H) := by
  have h := (pullback.snd H.hom a).finite_preimage
    (Set.toFinite (Set.univ : Set (Spec (.of K))))
  simp only [Set.preimage_univ] at h
  have : Finite (pullback H.hom a : Scheme.{u}) := Set.finite_univ_iff.mp h
  exact Finite.of_equiv _
    ((fieldPointPullbackEquiv H a).trans (pointEquivClosedPoint (pullback.snd H.hom a))).symm

theorem power_comp {S : Scheme.{u}} (A : Over S) [GrpObj A] (m n : ℕ) :
    ((𝟙 A : A ⟶ A) ^ m) ≫ ((𝟙 A : A ⟶ A) ^ n) = (𝟙 A : A ⟶ A) ^ (m * n) := by
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]

theorem power_point_eq_of_dvd {S : Scheme.{u}} (A : Over S) [GrpObj A]
    {m n : ℕ} (hmn : m ∣ n) {x y : A.left}
    (hxy : ((𝟙 A : A ⟶ A) ^ m).left x = ((𝟙 A : A ⟶ A) ^ m).left y) :
    ((𝟙 A : A ⟶ A) ^ n).left x = ((𝟙 A : A ⟶ A) ^ n).left y := by
  obtain ⟨k, rfl⟩ := hmn
  rw [← power_comp A m k]
  exact congrArg ((𝟙 A : A ⟶ A) ^ k).left hxy

/-- Each point of the translation relation is identified by some positive
multiplication map. No annihilation hypothesis is imposed on the subgroup. -/
theorem exists_power_eq {S : Scheme.{u}} {A H : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj H] [IsFinite H.hom]
    (i : H ⟶ A) [IsMonHom i] (r : (H ⊗ A).left) :
    ∃ n : ℕ, 0 < n ∧
      ((𝟙 A : A ⟶ A) ^ n).left ((Epi.Construction.translation i).left r) =
        ((𝟙 A : A ⟶ A) ^ n).left ((snd H A).left r) := by
  let K := AlgebraicClosure ((H ⊗ A).left.residueField r)
  let z : Spec (.of K) ⟶ (H ⊗ A).left :=
    Spec.map (CommRingCat.ofHom (algebraMap ((H ⊗ A).left.residueField r) K)) ≫
      (H ⊗ A).left.fromSpecResidueField r
  let T := Over.mk (z ≫ (H ⊗ A).hom)
  let z' : T ⟶ H ⊗ A := Over.homMk z rfl
  have : Finite (T ⟶ H) := finite_fieldPoints H (z ≫ (H ⊗ A).hom)
  let n := Nat.card (T ⟶ H)
  have hn : 0 < n := Nat.card_pos
  have he : z' ≫ Epi.Construction.translation i ≫ (𝟙 A : A ⟶ A) ^ n =
      z' ≫ snd H A ≫ (𝟙 A : A ⟶ A) ^ n := by
    simp only [← Category.assoc, MonObj.comp_pow, Category.comp_id,
      Epi.Construction.translation, MonObj.comp_mul, mul_pow]
    rw [← MonObj.pow_comp, show (z' ≫ fst H A) ^ n = 1 from pow_card_eq_one',
      MonObj.one_comp, one_mul]
  have hz : z (IsLocalRing.closedPoint K) = r := (H ⊗ A).left.fromSpecResidueField_apply r _
  refine ⟨n, hn, ?_⟩
  have he' := congrArg (fun f : Spec (.of K) ⟶ A.left => f (IsLocalRing.closedPoint K))
    (congrArg Over.Hom.left he)
  change ((𝟙 A : A ⟶ A) ^ n).left ((Epi.Construction.translation i).left (z (IsLocalRing.closedPoint K))) =
    ((𝟙 A : A ⟶ A) ^ n).left ((snd H A).left (z (IsLocalRing.closedPoint K))) at he'
  rwa [hz] at he'

/-- One positive integer collapses the entire finite orbit of a point. -/
theorem exists_power_constant_on_orbit {S : Scheme.{u}} {A H : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj H] [IsFinite H.hom]
    (i : H ⟶ A) [IsMonHom i] (x : A.left) :
    ∃ n : ℕ, 0 < n ∧ ∀ y, Invariant.Construction.InvariantCore.Related (snd H A).left (Epi.Construction.translation i).left x y →
      ((𝟙 A : A ⟶ A) ^ n).left y = ((𝟙 A : A ⟶ A) ^ n).left x := by
  classical
  have : IsFinite (snd H A).left := inferInstanceAs (IsFinite (pullback.snd H.hom A.hom))
  let F := (snd H A).left ⁻¹' ({x} : Set A.left)
  have hF : F.Finite := (snd H A).left.finite_preimage_singleton x
  let := hF.fintype
  choose n hn he using (fun r : F => exists_power_eq i r.val)
  let N := ∏ r : F, n r
  refine ⟨N, Finset.prod_pos (fun r _ => hn r), ?_⟩
  rintro y ⟨r, hr, rfl⟩
  have hd : n ⟨r, hr⟩ ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ (⟨r, hr⟩ : F))
  have he' := power_point_eq_of_dvd A hd (he ⟨r, hr⟩)
  rwa [hr] at he'

theorem exists_affine_orbit_of_finite_powers {S : Scheme.{u}} {A H : Over S}
    [GrpObj A] [IsCommMonObj A] [GrpObj H] [IsFinite H.hom]
    (i : H ⟶ A) [IsMonHom i]
    (hpow : ∀ n : ℕ, 0 < n → IsFinite ((𝟙 A : A ⟶ A) ^ n).left)
    (x : A.left) :
    ∃ U : A.left.Opens, IsAffineOpen U ∧
      ∀ y, Invariant.Construction.InvariantCore.Related (snd H A).left (Epi.Construction.translation i).left x y → y ∈ U := by
  obtain ⟨n, hn, he⟩ := exists_power_constant_on_orbit i x
  have := hpow n hn
  obtain ⟨U, hU, hx, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens
    (show ((𝟙 A : A ⟶ A) ^ n).left x ∈ (⊤ : A.left.Opens) from trivial)
  refine ⟨((𝟙 A : A ⟶ A) ^ n).left ⁻¹ᵁ U, hU.preimage _, ?_⟩
  intro y hy
  change ((𝟙 A : A ⟶ A) ^ n).left y ∈ U
  rw [he y hy]
  exact hx

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerOrbitEq.Construction.PowerOrbit
