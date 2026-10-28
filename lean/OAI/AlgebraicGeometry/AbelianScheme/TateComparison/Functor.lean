import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Rational

/-! # Functor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor

noncomputable section

/-! Functoriality and absence of torsion in the actual Tate inverse limit.
These statements use its torsion points and transition maps directly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Tate

variable (q : ℕ) [Fact q.Prime] {H H' H'' : Type u}
  [AddCommGroup H] [AddCommGroup H'] [AddCommGroup H'']

theorem map_id : Add.Tate.map q (AddMonoidHom.id H) = LinearMap.id := by
  ext x n
  rfl

theorem map_comp (f : H →+ H') (g : H' →+ H'') :
    Add.Tate.map q (g.comp f) = (Add.Tate.map q g).comp (Add.Tate.map q f) := by
  ext x n
  rfl

theorem map_add (f g : H →+ H') : Add.Tate.map q (f + g) = Add.Tate.map q f + Add.Tate.map q g := by
  ext x n
  rfl

theorem map_nsmul (n : ℕ) (f : H →+ H') : Add.Tate.map q (n • f) = n • Add.Tate.map q f := by
  ext x k
  rfl

theorem transition_iterate (x : Add.Tate.Module (H := H) q) (n k : ℕ) :
    q ^ k • (x.val (n + k)).val = (x.val n).val := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := congrArg Subtype.val (x.property (n + k))
    change q • (x.val (n + k + 1)).val = (x.val (n + k)).val at ht
    rw [pow_succ', mul_nsmul, ← Nat.add_assoc, ht, ih]

theorem q_smul_eq_zero (x : Add.Tate.Module (H := H) q) (h : (q : ℤ_[q]) • x = 0) : x = 0 := by
  rw [Nat.cast_smul_eq_nsmul] at h
  apply Subtype.ext
  funext n
  apply Subtype.ext
  have hz : q • (x.val (n + 1)).val = 0 :=
    congrArg (fun y : Add.Tate.Module (H := H) q => (y.val (n + 1)).val) h
  exact (congrArg Subtype.val (x.property n)).symm.trans hz

theorem q_pow_smul_eq_zero (n : ℕ) (x : Add.Tate.Module (H := H) q)
    (h : (q : ℤ_[q]) ^ n • x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', mul_smul] at h
    exact ih (q_smul_eq_zero q _ h)

theorem smul_eq_zero_of_ne_zero (z : ℤ_[q]) (hz : z ≠ 0)
    (x : Add.Tate.Module (H := H) q) (h : z • x = 0) : x = 0 := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz
    (PadicInt.irreducible_p (p := q))
  rw [mul_smul, u.isUnit.smul_eq_zero] at h
  exact q_pow_smul_eq_zero q n x h

instance moduleIsTorsionFree : _root_.Module.IsTorsionFree ℤ_[q] (Add.Tate.Module (H := H) q) :=
  _root_.Module.IsTorsionFree.of_smul_eq_zero fun z x h => by
    by_cases hz : z = 0
    · exact Or.inl hz
    · exact Or.inr (smul_eq_zero_of_ne_zero q z hz x h)

end Tate

variable {S : Scheme.{u}} {A B C : Over S}
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
  (T : Over S) (q : ℕ) [Fact q.Prime]

theorem schemeTateMap_id : Add.schemeTateMap A T q (𝟙 A) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrArg Additive.ofMul (Category.comp_id (x.val n).val.toMul)

theorem schemeTateMap_comp (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] :
    Add.schemeTateMap A T q (f ≫ g) = (Add.schemeTateMap B T q g).comp (Add.schemeTateMap A T q f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact congrArg Additive.ofMul (Category.assoc (x.val n).val.toMul f g).symm

theorem rationalTateMap_id : Rational.rationalTateMap (T := T) (q := q) (𝟙 A) = LinearMap.id := by
  rw [Rational.rationalTateMap, schemeTateMap_id, LinearMap.baseChange_id]

theorem rationalTateMap_comp (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C) [IsMonHom g] :
    Rational.rationalTateMap (T := T) (q := q) (f ≫ g) =
      (Rational.rationalTateMap (T := T) (q := q) g).comp (Rational.rationalTateMap (T := T) (q := q) f) := by
  rw [Rational.rationalTateMap, schemeTateMap_comp, LinearMap.baseChange_comp]
  rfl

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Functor
