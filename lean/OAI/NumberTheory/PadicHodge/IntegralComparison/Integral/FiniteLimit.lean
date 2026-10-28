import OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CocycleLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCocycleClasses
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection

/-! # Finite Limit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FiniteLimit

noncomputable section

/-! Every compatible family of actual finite-coefficient H¹ classes
comes from a unique actual integral H¹ class. The proof uses the genuine
simultaneous multiplication cover and integral cocycle descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacter OAI.NumberTheory.PadicHodge.IntegralComparison.CoverCharacterNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.CocycleLimit

universe u
variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [IsAlgClosed k]
  (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom]
  (hℓ : (ℓ : k) ≠ 0)

abbrev presentation : ShortComplex (Sheaf (Scheme.ProEt.topology A.left) Ab.{u + 1}) :=
  ShortComplex.mk _ _ (cokernel.condition (Injective.ι (AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.liftedEllAdicCoefficient ℓ A.left)))

omit [IsAlgClosed k] [GrpObj A] [IsCommMonObj A] [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] in
theorem presentation_shortExact : (presentation ℓ A).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (presentation ℓ A).f) }

local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.MultiplicationInfiniteCover.cover ℓ A hℓ
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.overlap ℓ A hℓ
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.first ℓ A hℓ
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.InfiniteMultiplicationOverlap.second ℓ A hℓ

include hℓ in
theorem exists_class
    (x : ∀ n, (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (hx : ∀ n, Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1
      (x (n + 1)) = x n) :
    ∃ z : A.left.EllAdicCohomology ℓ 1, ∀ n, AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 z = x n := by
  let : Surjective (terminal.from U).left := InfiniteMultiplicationOverlap.terminal_from_surjective ℓ A hℓ
  let : QuasiCompact (terminal.from U).left := InfiniteMultiplicationOverlap.terminal_from_quasiCompact ℓ A hℓ
  let S := presentation ℓ A
  let hS := presentation_shortExact ℓ A
  obtain ⟨z, r, hc⟩ := CoverCocycleClasses.exists_representative U D a b
    (InfiniteMultiplicationOverlap.isPullback ℓ A hℓ) S hS (CocycleLimit.integralCocycle ℓ A hℓ x hx)
    (CocycleLimit.integralCocycle_condition ℓ A hℓ x hx)
  refine ⟨z, fun n => ?_⟩
  let T := Finite.CoverCharacter.presentation ℓ n A.left
  let hT := Finite.CoverCharacter.presentation_shortExact ℓ n (X := A.left)
  obtain ⟨φ, hφ⟩ := InjectivePresentationMorphism.exists_morphism hS (T := T)
    (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicReduction ℓ n A.left)
  let rRed := CoverCharacterNaturality.mapRepresentative hS hT φ U D U D a b a b (𝟙 U) (𝟙 D) (by simp) (by simp) r
  let V := MultiplicationCoverCharacter.cover ℓ n A hℓ
  let E := MultiplicationCoverCharacter.overlap ℓ n A hℓ
  let c := MultiplicationCoverCharacter.first ℓ n A hℓ
  let d := MultiplicationCoverCharacter.second ℓ n A hℓ
  let hTlifts := Finite.CoverFiniteness.presentation_local_lifts ℓ n T.X₂ T.X₃ T.f T.g T.zero hT V
    (FiniteCoefficient.GroupLaw.multiplication_pow_pullback_zero ℓ n A)
  let rFin := CoverCharacter.representative T hT V E c d hTlifts (x n)
  let rRef := CoverCharacterNaturality.mapRepresentative hT hT (𝟙 T) V E U D c d a b
    (MultiplicationInfiniteCover.coverMap ℓ A hℓ n) (InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n)
    (InfiniteMultiplicationOverlap.overlapMap_first ℓ A hℓ n) (InfiniteMultiplicationOverlap.overlapMap_second ℓ A hℓ n) rFin
  have he : rRed.c = rRef.c := by
    change φ.τ₁.hom.app (op D) (S.X₁.obj.map (𝟙 D).op r.c) =
      (𝟙 T.X₁ : T.X₁ ⟶ T.X₁).hom.app (op D)
        (T.X₁.obj.map (InfiniteMultiplicationOverlap.overlapMap ℓ A hℓ n).op rFin.c)
    rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, hφ, hc]
    exact CocycleLimit.integralCocycle_reduction ℓ A hℓ x hx n
  have heq := CoverCocycleClasses.class_eq_of_cocycle_eq U D a b
    (InfiniteMultiplicationOverlap.isPullback ℓ A hℓ) T hT rRed rRef he
  change Sheaf.H.map φ.τ₁ 1 z = Sheaf.H.map (𝟙 T.X₁) 1 (x n) at heq
  rw [hφ, Sheaf.H.map_id_apply] at heq
  exact heq

include hℓ in
theorem existsUnique_class
    (x : ∀ n, (AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n A.left).H 1)
    (hx : ∀ n, Sheaf.H.map (AlgebraicGeometry.FormalGeometry.Completion.CoefficientSheafLimit.Construction.finiteEllAdicTransition ℓ n (n + 1) (Nat.le_succ n) A.left) 1
      (x (n + 1)) = x n) :
    ∃! z : A.left.EllAdicCohomology ℓ 1, ∀ n, AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientCohomology.Construction.integralEllAdicFiniteReduction ℓ n A.left 1 z = x n := by
  obtain ⟨z, hz⟩ := exists_class ℓ A hℓ x hx
  exact ⟨z, hz, fun y hy => AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientDetection.Construction.integralEllAdicH1_ext_finiteReduction ℓ A.left y z
    (fun n => (hy n).trans (hz n).symm)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Integral.FiniteLimit
