import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NeutralCharacters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.TorsionFinite

/-! # Torsion Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCharacters.CM

noncomputable section

/-! Character restriction is injective for the original ordinary abelian
torsion scheme at every level. No character matching is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

omit [IsAlgClosed k] in
theorem points_killed (m : ℕ) (T : Over (Spec (.of k)))
    (p : T ⟶ A.torsionScheme m) : p ^ m = 1 := by
  let e : (T ⟶ A.torsionScheme m) ≃* A.torsionPoints m T :=
    ((A.torsionSchemeYonedaIso m).app (.op T)).groupIsoToMulEquiv
  apply e.injective
  rw [map_pow, map_one]
  apply Subtype.ext
  exact (e p).property

omit [IsAlgClosed k] in
theorem subgroup_points_killed (m : ℕ) (B : Grp (Over (Spec (.of k))))
    (i : B ⟶ @Grp.mk _ _ _ (A.torsionScheme m) (A.torsionScheme_group m))
    [Mono i.hom.hom] (T : Over (Spec (.of k))) (p : T ⟶ B.X) : p ^ m = 1 := by
  apply (cancel_mono i.hom.hom).mp
  exact (MonObj.pow_comp p m i.hom.hom).trans
    ((points_killed A m T (p ≫ i.hom.hom)).trans (MonObj.one_comp i.hom.hom).symm)

theorem restriction_injective (q : ℕ) [Fact q.Prime] [CharP k q]
    (hordinary : Nat.card (A.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (n : ℕ) :
    letI : IsFinite (A.torsionScheme (q ^ n)).hom :=
      Ordinary.TorsionFinite.CM.torsion_finite A q hordinary n
    Function.Injective (NeutralCharacters.CM.restrict
      (@Grp.mk _ _ _ (A.torsionScheme (q ^ n)) (A.torsionScheme_group (q ^ n)))) := by
  let : IsFinite (A.torsionScheme (q ^ n)).hom :=
    Ordinary.TorsionFinite.CM.torsion_finite A q hordinary n
  let Tor : Grp (Over (Spec (.of k))) := Grp.mk (A.torsionScheme (q ^ n))
  let : IsFinite Tor.X.hom := Ordinary.TorsionFinite.CM.torsion_finite A q hordinary n
  let : IsCommMonObj Tor.X := A.torsionScheme_commutative (q ^ n)
  exact NeutralCharacters.CM.restrict_injective Tor q n
    (points_killed A (q ^ n) (Over.mk (𝟙 (Spec (.of k)))))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCharacters.CM
