import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientEndomorphismDescent
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientFiberRecovery

/-! # Field Endomorphism Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldEndomorphismDescent.FieldDescent

noncomputable section

/-! Group endomorphisms of an abelian variety acquire no new maps under
extension of an algebraically closed ground field. Finite coefficient
spreading, an actual parameter point, and proper-family rigidity construct
the descended endomorphism and its exact base-change equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.CoefficientFiberRecovery

variable (k B : Type) [Field k] [IsAlgClosed k] [Field B] [Algebra k B]
  {g : ℕ} (A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))

theorem field_endomorphism_descends
    (a : (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme ⟶
      (A.pullback (Spec.map (CommRingCat.ofHom (algebraMap k B)))).scheme)
    [IsMonHom a] :
    ∃ f : A.scheme ⟶ A.scheme, IsMonHom f ∧
      ArithmeticGeometry.Descent.CMVariety.CoefficientEndomorphismComparison.Abelian.abelianPullbackEndomorphism A (Spec.map (CommRingCat.ofHom (algebraMap k B))) f = a := by
  obtain ⟨s, t, c, hc⟩ := ArithmeticGeometry.Descent.CMVariety.AbelianEndomorphism.finite_abelian_group_endomorphisms_spread k B A (fun _ : Unit => a)
  have : IsMonHom (c ()) := (hc ()).1
  obtain ⟨f, hf, hfc⟩ := CoefficientEndomorphismDescent.FieldDescent.coefficient_endomorphism_descends_to_base k B A s t (c ())
  exact ⟨f, hf, AbelianScheme.TateComparison.CoefficientFiberRecovery.coefficient_fiber_recovery k B A s t f (c ()) a hfc (hc ()).2⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldEndomorphismDescent.FieldDescent
