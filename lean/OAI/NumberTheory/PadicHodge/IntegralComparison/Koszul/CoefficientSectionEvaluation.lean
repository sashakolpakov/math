import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientPointFraction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.SectionCoefficient

/-! # Coefficient Section Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientSectionEvaluation

noncomputable section

/-! Point evaluation supplies its own canonical base coefficient; no
ambient lift of a coefficient value is an additional premise. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
  {c m : ℕ} (s : Fin c → R) (t : Fin m → R)
  (e₀ : (R ⧸ KoszulPartial.Resolution.pointIdeal R s t) ≃ₐ[k] k)
  (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M]
  [IsScalarTower R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M]
  (ε : M →ₗ[R] (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)) (v : M)

def scalar : R := algebraMap k R (e₀ (ε v))

omit [Module (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M] [IsScalarTower R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M] in
theorem scalar_value : ε v = Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t)
    (scalar k R s t e₀ M ε v) := by
  apply e₀.injective
  change e₀ (ε v) = e₀ (algebraMap k (R ⧸ KoszulPartial.Resolution.pointIdeal R s t) (e₀ (ε v)))
  exact (e₀.commutes (e₀ (ε v))).symm

theorem weight : CoefficientPointFraction.vector R s M v ≫
    CoefficientPointFraction.coefficient R s t M ε =
      scalar k R s t e₀ M ε v • KoszulPartial.Resolution.quotient R s t :=
  CoefficientPointFraction.weight R s t M ε v _ (scalar_value k R s t e₀ M ε v)

variable (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (PM : ProjectiveResolution (ModuleCat.of R M))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R) (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev homotopy := CoefficientPointFraction.homotopy R s t hs hst M PM ε v P
  (scalar k R s t e₀ M ε v) (scalar_value k R s t e₀ M ε v)

abbrev class_eq (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :=
  CoefficientPointFraction.class_eq R s t hs hst M PM ε v P U ht
    (scalar k R s t e₀ M ε v) (scalar_value k R s t e₀ M ε v) φ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientSectionEvaluation
