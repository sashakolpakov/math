import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Subgroup

/-! # Split Subgroups -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups

noncomputable section

/-! The split torsion eigensubgroups are preserved by PEL isomorphisms
and by base change, with the given integral local characters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {R : Type u} [CommRing R] {g N q : ℕ} [Fact q.Prime] {S S' : Scheme.{u}}

theorem splitBlock_comapIso {A B : PEL.PELFamilyData R g N S}
    (e : PELModuli.PELFamilyIso A B) (χ : R →+* ℤ_[q]) (h : ℕ) :
    (Subgroups.splitBlock B χ h).comapHom e.abelian.hom = Subgroups.splitBlock A χ h := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  change ((x ≫ e.abelian.hom) ^ (q ^ h) = 1 ∧ ∀ r : R,
    (x ≫ e.abelian.hom) ≫ End.endSchemeMap B.abelian.scheme (B.action r) =
      (x ≫ e.abelian.hom) ^ (PadicInt.toZModPow h (χ r)).val) ↔
    (x ^ (q ^ h) = 1 ∧ ∀ r : R,
      x ≫ End.endSchemeMap A.abelian.scheme (A.action r) =
        x ^ (PadicInt.toZModPow h (χ r)).val)
  have hk : (x ≫ e.abelian.hom) ^ (q ^ h) = 1 ↔ x ^ (q ^ h) = 1 := by
    rw [← MonObj.pow_comp, ← MonObj.one_comp e.abelian.hom]
    exact cancel_mono e.abelian.hom
  refine and_congr hk (forall_congr' fun r => ?_)
  rw [Category.assoc, ← e.equivariant, ← Category.assoc, ← MonObj.pow_comp]
  exact cancel_mono e.abelian.hom

theorem splitBlock_pullback (A : PEL.PELFamilyData R g N S)
    (χ : R →+* ℤ_[q]) (h : ℕ) (s : S' ⟶ S) :
    (Subgroups.splitBlock A χ h).pullback s = Subgroups.splitBlock (A.pullback s) χ h := by
  apply Subgroups.PointSubgroup.ext
  intro T
  ext x
  let e := A.abelian.baseChangePointsMulEquiv s T
  have hact (r : R) :
      e (x ≫ End.endSchemeMap (A.pullback s).abelian.scheme ((A.pullback s).action r)) =
        e x ≫ End.endSchemeMap A.abelian.scheme (A.action r) :=
    (congrArg (fun z => A.abelian.baseChangePointsEquiv s T (x ≫ z))
      (A.pullback_action_schemeMap s r)).trans
        (AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.baseChangePointsEquiv_map (End.endSchemeMap A.abelian.scheme (A.action r)) s T x)
  change ((e x) ^ (q ^ h) = 1 ∧ ∀ r : R,
    e x ≫ End.endSchemeMap A.abelian.scheme (A.action r) =
      (e x) ^ (PadicInt.toZModPow h (χ r)).val) ↔
    (x ^ (q ^ h) = 1 ∧ ∀ r : R,
      x ≫ End.endSchemeMap (A.pullback s).abelian.scheme ((A.pullback s).action r) =
        x ^ (PadicInt.toZModPow h (χ r)).val)
  have hk : (e x) ^ (q ^ h) = 1 ↔ x ^ (q ^ h) = 1 := by
    rw [← map_pow]
    exact e.map_eq_one_iff
  refine and_congr hk (forall_congr' fun r => ?_)
  rw [← hact, ← map_pow]
  exact e.injective.eq_iff

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.SplitSubgroups
