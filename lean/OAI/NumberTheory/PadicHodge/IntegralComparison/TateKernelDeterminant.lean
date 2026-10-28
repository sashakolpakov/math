import OAI.NumberTheory.PadicHodge.IntegralComparison.CokernelDeterminant
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration

/-! # Tate Kernel Determinant -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TateKernelDeterminant

noncomputable section

/-! For an actual homomorphism with a complementary prime-power map,
the cardinality of its kernel equals the determinant index of its Tate
map. The Tate module is the original inverse limit of torsion points. -/

variable (p h : ℕ) [Fact p.Prime] {A : Type*} [AddCommGroup A]
  (f g : A →+ A)

theorem tateMap_injective
    (hgf : ∀ x, g (f x) = (p ^ h) • x) : Function.Injective (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply AlgebraicGeometry.AbelianScheme.TateComparison.Functor.Tate.q_pow_smul_eq_zero p h (x - y)
  have hz : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hc := AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel.Construction.tate_complementary_map p h f g hgf (x - y)
  rw [hz, map_zero] at hc
  exact hc.symm

theorem kernel_card [Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p A 1)]
    (hfg : ∀ y, f (g y) = (p ^ h) • y)
    (hgf : ∀ x, g (f x) = (p ^ h) • x)
    (hf : Function.Surjective f) (hdiv : ∀ x : A, ∃ y, p • y = x) :
    Nat.card f.ker = p ^ (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det.valuation := by
  let : Module.Finite ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := A) p) :=
    AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion p hdiv
  let e := AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TateCokernel.Construction.tateCokernelKernelEquiv p h f g hfg hgf hf hdiv
  exact (Nat.card_congr e.toEquiv).symm.trans
    (CokernelDeterminant.cokernel_card p (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f)
      (tateMap_injective p h f g hgf))

section CoprimeFactor

variable (c : ℕ) (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) = c)

theorem complementary_map
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x))
    (x : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := A) p) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p g (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f x) =
      (c : ℤ_[p]) • ((p : ℤ_[p]) ^ h • x) := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  apply Subtype.ext
  funext n
  apply Subtype.ext
  exact hgf (x.val n).val

def primaryConnectingMap
    (hfg : ∀ x, f (g x) = c • ((p ^ h) • x)) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := A) p →+ AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h where
  toFun x := ⟨⟨g (x.val h).val, by
    change f (g (x.val h).val) = 0
    rw [hfg, (x.val h).property, nsmul_zero]⟩, by
    apply Subtype.ext
    change (p ^ h) • g (x.val h).val = 0
    rw [← map_nsmul, (x.val h).property, map_zero]⟩
  map_zero' := Subtype.ext (Subtype.ext g.map_zero)
  map_add' x y := Subtype.ext (Subtype.ext (g.map_add (x.val h).val (y.val h).val))

include u hu

theorem primaryConnectingMap_ker
    (hfg : ∀ x, f (g x) = c • ((p ^ h) • x))
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x)) :
    (primaryConnectingMap p h f g c hfg).ker = (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).toAddMonoidHom.range := by
  ext b
  change primaryConnectingMap p h f g c hfg b = 0 ↔ ∃ a, AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f a = b
  constructor
  · intro hb
    have hbval : g (b.val h).val = 0 :=
      congrArg (fun z : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h => z.val.val) hb
    have heval : AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate p h (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p g b) = 0 := Subtype.ext hbval
    obtain ⟨a, ha⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_eq_zero_iff p h (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p g b)).mp heval
    have he : (p : ℤ_[p]) ^ h • AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f a =
        (p : ℤ_[p]) ^ h • ((c : ℤ_[p]) • b) := by
      rw [← map_smul, ha, complementary_map p h g f c hfg, smul_comm]
    have hfa : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f a = (c : ℤ_[p]) • b := by
      apply sub_eq_zero.mp
      apply AlgebraicGeometry.AbelianScheme.TateComparison.Functor.Tate.q_pow_smul_eq_zero p h (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f a - (c : ℤ_[p]) • b)
      rw [smul_sub, he, sub_self]
    refine ⟨(↑u⁻¹ : ℤ_[p]) • a, ?_⟩
    rw [map_smul, hfa, ← hu, smul_smul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_smul]
  · rintro ⟨a, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    change g (f (a.val h).val) = 0
    rw [hgf, (a.val h).property, nsmul_zero]

theorem primaryConnectingMap_surjective
    (hfg : ∀ x, f (g x) = c • ((p ^ h) • x))
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x))
    (hdiv : ∀ x : A, ∃ y, p • y = x) :
    Function.Surjective (primaryConnectingMap p h f g c hfg) := by
  intro z
  let w : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h := (↑u⁻¹ : ℤ_[p]) • z
  have hcw : c • w = z := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← hu]
    change (u : ℤ_[p]) • ((↑u⁻¹ : ℤ_[p]) • z) = z
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let y := AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.divisionChain p hdiv w.val.val h
  have hy : (p ^ h) • y = w.val.val := AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.divisionChain_iterate p hdiv w.val.val h
  let b : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p A h := ⟨f y, by
    change (p ^ h) • f y = 0
    rw [← map_nsmul, hy]
    exact w.val.property⟩
  obtain ⟨t, ht⟩ := AlgebraicGeometry.AbelianScheme.TateComparison.Evaluation.Tate.evaluate_surjective p hdiv h b
  refine ⟨t, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change g (t.val h).val = z.val.val
  have hb : (t.val h).val = f y := congrArg Subtype.val ht
  rw [hb, hgf, hy]
  exact congrArg (fun a : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h => a.val.val) hcw

theorem primary_tateMap_injective
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x)) :
    Function.Injective (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f) := by
  intro x y hxy
  apply sub_eq_zero.mp
  have hz : AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hc := complementary_map p h f g c hgf (x - y)
  rw [hz, map_zero, ← hu] at hc
  exact AlgebraicGeometry.AbelianScheme.TateComparison.Functor.Tate.q_pow_smul_eq_zero p h (x - y) (u.isUnit.smul_eq_zero.mp hc.symm)

theorem primary_kernel_card [Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p A 1)]
    (hfg : ∀ x, f (g x) = c • ((p ^ h) • x))
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x))
    (hdiv : ∀ x : A, ∃ y, p • y = x) :
    Nat.card (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h) = p ^ (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det.valuation := by
  let : Module.Finite ℤ_[p] (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.Module (H := A) p) :=
    AlgebraicGeometry.AbelianScheme.TateComparison.FiniteGeneration.Tate.finite_of_finite_torsion p hdiv
  let δ := primaryConnectingMap p h f g c hfg
  let e := (QuotientAddGroup.quotientAddEquivOfEq
      (primaryConnectingMap_ker p h f g c u hu hfg hgf).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective δ
      (primaryConnectingMap_surjective p h f g c u hu hfg hgf hdiv))
  exact (Nat.card_congr e.toEquiv).symm.trans
    (CokernelDeterminant.cokernel_card p (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f)
      (primary_tateMap_injective p h f g c u hu hgf))

end CoprimeFactor

theorem primary_kernel_card_of_coprime [Finite (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p A 1)]
    (c : ℕ) (hc : p.Coprime c)
    (hfg : ∀ x, f (g x) = c • ((p ^ h) • x))
    (hgf : ∀ x, g (f x) = c • ((p ^ h) • x))
    (hdiv : ∀ x : A, ∃ y, p • y = x) :
    Nat.card (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.torsion p f.ker h) = p ^ (AlgebraicGeometry.AbelianScheme.TateComparison.Add.Tate.map p f).det.valuation := by
  obtain ⟨u, hu⟩ : IsUnit (c : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hc)
  exact primary_kernel_card p h f g c u hu hfg hgf hdiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TateKernelDeterminant
