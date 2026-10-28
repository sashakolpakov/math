import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Field.Equiv

/-! # Field Point -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint

noncomputable section

/-! The prime of global functions determined by a field-valued point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

namespace Construction.FieldPointPrime

abbrev sectionsField (K : Type u) [Field K] : Field Γ(Spec (.of K), ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField

theorem kernel {S : Scheme.{u}} {K : Type u} [Field K] (g : Spec (.of K) ⟶ S)
    (t : Spec (.of K)) : (S.toSpecΓ (g t)).asIdeal = RingHom.ker g.appTop.hom := by
  let : Field Γ(Spec (.of K), ⊤) := sectionsField K
  have hn := congrArg (fun a : Spec (.of K) ⟶ Spec Γ(S, ⊤) => a t)
    (Scheme.toSpecΓ_naturality g)
  change S.toSpecΓ (g t) = Spec.map g.appTop ((Spec (.of K)).toSpecΓ t) at hn
  rw [hn]
  change Ideal.comap g.appTop.hom (((Spec (.of K)).toSpecΓ t).asIdeal) = _
  let q : PrimeSpectrum Γ(Spec (.of K), ⊤) := (Spec (.of K)).toSpecΓ t
  have : q.asIdeal.IsPrime := q.isPrime
  have hb : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  exact congrArg (Ideal.comap g.appTop.hom) hb

end Construction.FieldPointPrime

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FieldPoint
