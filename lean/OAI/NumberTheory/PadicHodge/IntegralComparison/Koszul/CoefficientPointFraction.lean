import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientEvaluationHomotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.Quotient.CoefficientEvaluation

/-! # Coefficient Point Fraction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientPointFraction

noncomputable section

/-! Evaluating an actual quotient-module point class on a coefficient
vector gives exactly its point value times the canonical supported
fraction. The resolution maps are genuine canonical augmentation lifts. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Fractions OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Components OAI.NumberTheory.PadicHodge.IntegralComparison.KoszulPartial.Resolution
variable (R : Type u) [CommRing R] {c m : ℕ} (s : Fin c → R) (t : Fin m → R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (hst : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.append s t)))
  (M : Type u) [AddCommGroup M] [Module R M] [Module (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M]
  [IsScalarTower R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M]
  (PM : ProjectiveResolution (ModuleCat.of R M))
  (ε : M →ₗ[R] (R ⧸ KoszulPartial.Resolution.pointIdeal R s t)) (v : M)

 def coefficient : ModuleCat.of R M ⟶ ModuleCat.of R (R ⧸ KoszulPartial.Resolution.pointIdeal R s t) :=
  ModuleCat.ofHom ε

 def vector : ModuleCat.of R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) ⟶ ModuleCat.of R M :=
  IntegralComparison.Quotient.CoefficientEvaluation.point R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) M v

 theorem weight (r : R) (hr : ε v = Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) r) :
    vector R s M v ≫ coefficient R s t M ε = r • KoszulPartial.Resolution.quotient R s t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  change ε ((algebraMap R (R ⧸ KoszulPartial.Resolution.normalIdeal R s) x) • v) = _
  rw [IsScalarTower.algebraMap_smul, ε.map_smul, hr]
  change (Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) x) * (Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) r) =
    (Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) r) * (Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) x)
  exact mul_comm _ _

 def pointLift := ProjectiveResolution.lift (coefficient R s t M ε) PM (KoszulPartial.Resolution.pointResolution R s t hst)
 def vectorLift := ProjectiveResolution.lift (vector R s M v) (KoszulPartial.Resolution.normalResolution R s hs) PM

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  (P : Cᵒᵖ ⥤ CommAlgCat.{u} R)
  (U : ULift.{u} (Fin m) → C)
  (ht : ∀ i, IsUnit (algebraMap R (P.obj (op (U i))) (t i.down)))

abbrev pointMap := CoefficientEvaluationHomotopy.pointMap R P s t hst
  (ModuleCat.of R M) PM (pointLift R s t hst M PM ε)
abbrev evaluation := CoefficientEvaluationHomotopy.evaluation R P s hs
  (ModuleCat.of R M) PM (vectorLift R s hs M PM v)

abbrev homotopy (r : R) (hr : ε v = Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) r) :=
  CoefficientEvaluationHomotopy.homotopy R P s t hs hst (ModuleCat.of R M) PM
    (coefficient R s t M ε) (vector R s M v)
    (pointLift R s t hst M PM ε) (vectorLift R s hs M PM v)
    (ProjectiveResolution.lift_commutes (coefficient R s t M ε) PM (KoszulPartial.Resolution.pointResolution R s t hst))
    (ProjectiveResolution.lift_commutes (vector R s M v) (KoszulPartial.Resolution.normalResolution R s hs) PM)
    r (weight R s t M ε v r hr)

abbrev class_eq (r : R) (hr : ε v = Ideal.Quotient.mk (KoszulPartial.Resolution.pointIdeal R s t) r)
    (φ : Module.Dual R (⋀[R]^(c+m) (KoszulPartial.Fractions.ambient R (c := c) (m := m)))) :=
  SupportedCoefficientEvaluation.class_eq R P U s t ht
    (pointMap R s t hst M PM ε P) (evaluation R s hs M PM v P)
    r (homotopy R s t hs hst M PM ε v P r hr) φ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.CoefficientPointFraction
