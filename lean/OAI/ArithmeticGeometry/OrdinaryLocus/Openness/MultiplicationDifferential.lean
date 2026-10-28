import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.InfinitesimalPowerEq
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalFirstOrder
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffinePointCard
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.Multiplication
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LocalizationDifferential

/-! # Multiplication Differential -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDifferential.Construction

noncomputable section

/-! Vanishing of the differential of multiplication by p on actual affine charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

/-- Pulling back a coordinate function along multiplication by p has zero
differential in every field-valued point of a source chart in characteristic p. -/
theorem differential_multiplication_chart
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (p : ℕ) [CharP L p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (R B : Type u) [CommRing R] [CommRing B] [Algebra k R] [Algebra k B]
    [Algebra B L] [IsScalarTower k B L]
    (i : Spec (.of R) ⟶ A.left) (j : Spec (.of B) ⟶ A.left) [Mono i]
    (hj : j ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (φ : R →ₐ[k] B)
    (hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i =
      j ≫ (Multiplication.Construction.multiplicationMap A p).left) (r : R) :
    KaehlerDifferential.D k L (algebraMap B L (φ r)) = 0 := by
  let M := KaehlerDifferential k L
  let : Module Lᵐᵒᵖ M := Module.compHom _ ((RingHom.id L).fromOpposite mul_comm)
  have : IsCentralScalar L M := ⟨fun _ _ => rfl⟩
  let C := TrivSqZeroExt L M
  have : IsLocalRing C := UniversalFirstOrder.Construction.isLocalRing_trivSqZeroExt L M
  have : CharP C p := UniversalFirstOrder.Construction.charP_trivSqZeroExt L M p
  let J := TrivSqZeroExt.kerIdeal L M
  have hJ : J ^ 2 = ⊥ := TrivSqZeroExt.kerIdeal_sq L M
  let d₁ := UniversalFirstOrder.Construction.derivationFirstOrderHom k L M (KaehlerDifferential.D k L)
  let d₀ := TrivSqZeroExt.inlAlgHom k L M
  let b₁ : B →ₐ[k] C := d₁.comp (IsScalarTower.toAlgHom k B L)
  let b₀ : B →ₐ[k] C := d₀.comp (IsScalarTower.toAlgHom k B L)
  let s : Spec (.of C) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k C))
  let a₁ : Over.mk s ⟶ A :=
    (AffinePointCard.Construction.specPointsEquivAlgHom k B C).symm b₁ ≫ Over.homMk j hj
  let a₀ : Over.mk s ⟶ A :=
    (AffinePointCard.Construction.specPointsEquivAlgHom k B C).symm b₀ ≫ Over.homMk j hj
  have he : CommRingCat.ofHom b₁.toRingHom ≫
      CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom b₀.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    ext b
    apply Ideal.Quotient.eq.mpr
    change (b₁ b - b₀ b) ∈ RingHom.ker (TrivSqZeroExt.fstHom L L M)
    change (b₁ b - b₀ b).fst = 0
    change algebraMap B L b - algebraMap B L b = 0
    exact sub_self _
  have hred : InfinitesimalPowerEq.Construction.InfinitesimalPower.reduction s J A a₁ =
      InfinitesimalPowerEq.Construction.InfinitesimalPower.reduction s J A a₀ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
      (Spec.map (CommRingCat.ofHom b₁.toRingHom) ≫ j) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
        (Spec.map (CommRingCat.ofHom b₀.toRingHom) ≫ j)
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, he]
  have hp := InfinitesimalPowerEq.Construction.InfinitesimalPower.pow_eq_of_reduction_eq s J hJ A p a₁ a₀ hred
  have hp' : a₁ ≫ Multiplication.Construction.multiplicationMap A p = a₀ ≫ Multiplication.Construction.multiplicationMap A p := by
    simpa only [Multiplication.Construction.multiplicationMap, MonObj.comp_pow, Category.comp_id] using hp
  have hs := congrArg Over.Hom.left hp'
  change (Spec.map (CommRingCat.ofHom b₁.toRingHom) ≫ j) ≫
      (Multiplication.Construction.multiplicationMap A p).left =
      (Spec.map (CommRingCat.ofHom b₀.toRingHom) ≫ j) ≫
        (Multiplication.Construction.multiplicationMap A p).left at hs
  rw [Category.assoc, Category.assoc, ← hφ, ← Category.assoc, ← Category.assoc] at hs
  have hs' := (cancel_mono i).mp hs
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hs'
  have hr := congrArg (fun f => (f.hom r).snd) hs'
  exact hr

/-- The map of fraction fields induced by multiplication by p has zero
differential. The chart compatibility is an equality of actual scheme maps. -/
theorem map_kaehler_multiplication_fractionField_eq_zero
    {k K L : Type u} [Field k] [Field K] [Field L]
    (p : ℕ) [CharP L p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    (R B : Type u) [CommRing R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]
    [Algebra B L] [Algebra R L] [IsScalarTower R B L]
    [Algebra K L] [IsScalarTower R K L]
    [Algebra k L] [IsScalarTower k B L] [IsScalarTower k R L] [IsScalarTower k K L]
    (i : Spec (.of R) ⟶ A.left) (j : Spec (.of B) ⟶ A.left) [Mono i]
    (hj : j ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ i =
      j ≫ (Multiplication.Construction.multiplicationMap A p).left) :
    KaehlerDifferential.map k k K L = 0 := by
  apply LocalizationDifferential.Construction.map_kaehler_fractionField_eq_zero k R K L
  intro r
  rw [IsScalarTower.algebraMap_apply R B L]
  exact differential_multiplication_chart p A R B i j hj
    (IsScalarTower.toAlgHom k R B) hφ r

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.MultiplicationDifferential.Construction
