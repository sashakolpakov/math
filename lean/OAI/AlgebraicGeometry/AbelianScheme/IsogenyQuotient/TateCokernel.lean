import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Tate Cokernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel.Construction

noncomputable section

/-!
For an actual surjective homomorphism with complementary q^h maps,
the integral Tate cokernel is its original kernel. The connecting map
is evaluation at level h followed by the complementary homomorphism.
Its surjectivity and exact kernel are proved from divisibility and the
actual inverse-limit evaluation theorem.
-/

universe u

variable (q h : ℕ) [Fact q.Prime] {A B : Type u} [AddCommGroup A] [AddCommGroup B]
  (f : A →+ B) (g : B →+ A)

theorem tate_complementary_map (hgf : ∀ x, g (f x) = (q ^ h) • x)
    (x : TateComparison.Add.Tate.Module (H := A) q) :
    TateComparison.Add.Tate.map q g (TateComparison.Add.Tate.map q f x) = (q : ℤ_[q]) ^ h • x := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact hgf (x.val n).val

def tateConnectingMap (hfg : ∀ y, f (g y) = (q ^ h) • y) :
    TateComparison.Add.Tate.Module (H := B) q →+ f.ker where
  toFun x := ⟨g (x.val h).val, by
    change f (g (x.val h).val) = 0
    rw [hfg]
    exact (x.val h).property⟩
  map_zero' := Subtype.ext g.map_zero
  map_add' x y := Subtype.ext (g.map_add (x.val h).val (y.val h).val)

theorem tateConnectingMap_ker
    (hfg : ∀ y, f (g y) = (q ^ h) • y) (hgf : ∀ x, g (f x) = (q ^ h) • x) :
    (tateConnectingMap q h f g hfg).ker = (TateComparison.Add.Tate.map q f).toAddMonoidHom.range := by
  ext b
  change tateConnectingMap q h f g hfg b = 0 ↔ ∃ a, TateComparison.Add.Tate.map q f a = b
  constructor
  · intro hb
    have hbval : g (b.val h).val = 0 := congrArg (fun x : f.ker => x.val) hb
    have heval : TateComparison.Evaluation.Tate.evaluate q h (TateComparison.Add.Tate.map q g b) = 0 :=
      Subtype.ext hbval
    obtain ⟨a, ha⟩ := (TateComparison.Evaluation.Tate.evaluate_eq_zero_iff q h (TateComparison.Add.Tate.map q g b)).mp heval
    refine ⟨a, ?_⟩
    have he : (q : ℤ_[q]) ^ h • TateComparison.Add.Tate.map q f a = (q : ℤ_[q]) ^ h • b := by
      rw [← map_smul, ha, tate_complementary_map q h g f hfg]
    apply sub_eq_zero.mp
    apply TateComparison.Functor.Tate.q_pow_smul_eq_zero q h (TateComparison.Add.Tate.map q f a - b)
    rw [smul_sub, he, sub_self]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    change g (f (a.val h).val) = 0
    rw [hgf]
    exact (a.val h).property

theorem tateConnectingMap_surjective
    (hfg : ∀ y, f (g y) = (q ^ h) • y) (hgf : ∀ x, g (f x) = (q ^ h) • x)
    (hf : Function.Surjective f) (hdiv : ∀ x : A, ∃ y, q • y = x) :
    Function.Surjective (tateConnectingMap q h f g hfg) := by
  have hdivB (b : B) : ∃ y, q • y = b := by
    obtain ⟨a, ha⟩ := hf b
    obtain ⟨y, hy⟩ := hdiv a
    exact ⟨f y, by rw [← map_nsmul, hy, ha]⟩
  intro x
  let y := TateComparison.Evaluation.Tate.divisionChain q hdiv x.val h
  have hy : (q ^ h) • y = x.val := TateComparison.Evaluation.Tate.divisionChain_iterate q hdiv x.val h
  let b : TateComparison.Add.Tate.torsion q B h := ⟨f y, by
    change (q ^ h) • f y = 0
    rw [← map_nsmul, hy]
    exact x.property⟩
  obtain ⟨t, ht⟩ := TateComparison.Evaluation.Tate.evaluate_surjective q hdivB h b
  refine ⟨t, Subtype.ext ?_⟩
  change g (t.val h).val = x.val
  have hb : (t.val h).val = f y := congrArg Subtype.val ht
  rw [hb, hgf]
  exact hy

/-- The quotient is computed from the actual Tate map of f and identifies
canonically with the original kernel of f. -/
def tateCokernelKernelEquiv
    (hfg : ∀ y, f (g y) = (q ^ h) • y) (hgf : ∀ x, g (f x) = (q ^ h) • x)
    (hf : Function.Surjective f) (hdiv : ∀ x : A, ∃ y, q • y = x) :
    TateComparison.Add.Tate.Module (H := B) q ⧸ (TateComparison.Add.Tate.map q f).toAddMonoidHom.range ≃+ f.ker :=
  (QuotientAddGroup.quotientAddEquivOfEq (tateConnectingMap_ker q h f g hfg hgf).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (tateConnectingMap q h f g hfg)
      (tateConnectingMap_surjective q h f g hfg hgf hf hdiv))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel.Construction
