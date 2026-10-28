import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineMultiplicationBound
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AffineChartPullback
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ChartAlgebras
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TorsionGenericCount
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FieldReduction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Degree Reduction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DegreeReduction.Construction

noncomputable section

/-! Reducing the remaining Openness torsion bound to the total degree of multiplication. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem torsionPointCard_le_of_multiplication_degree
    {k : Type u} [Field k] [IsAlgClosed k]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsFinite (DefinitionsTorsion.Construction.torsionScheme A p).hom]
    (g : ℕ) (hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞))
    (hdegree : ∀ a : A.left, (Multiplication.Construction.multiplicationMap A p).left.finrank a = p ^ (2 * g)) :
    Nat.card {x : Over.mk (𝟙 (Spec (.of k))) ⟶ A // x ^ p = 1} ≤ p ^ g := by
  have : IsIntegral A.left := ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group A
  let f := (Multiplication.Construction.multiplicationMap A p).left
  have : IsFinite f := Multiplication.Construction.isFinite_multiplication_of_isFinite_torsion A p
  obtain ⟨hs, hf⟩ := FieldMultiplicationFlat.Construction.surjective_flat_multiplication_of_isFinite A p
  have : Surjective f := hs
  have : Flat f := hf
  have : LocallyOfFinitePresentation f := Openness.FinitePresentation.Construction.locallyOfFinitePresentation_multiplication A p
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  obtain ⟨_, ⟨U, hU, rfl⟩, hgen, _⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint A.left)) isOpen_univ
  change IsAffineOpen U at hU
  have : Nonempty U := ⟨⟨genericPoint A.left, hgen⟩⟩
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  obtain ⟨x, hx⟩ := f.surjective (genericPoint A.left)
  have : Nonempty V := ⟨⟨x, by change f x ∈ U; rwa [hx]⟩⟩
  let R := Γ(A.left, U)
  let B := Γ(A.left, V)
  let : Algebra k R := GroupFunctionField.Construction.chartAlgebra A.hom U hU
  let : Algebra k B := GroupFunctionField.Construction.chartAlgebra A.hom V hV
  let : Algebra R B := (f.app U).hom.toAlgebra
  have : IsScalarTower k R B := by
    apply IsScalarTower.of_algebraMap_eq'
    have hc : Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
      simpa only [V, Scheme.Hom.appLE_eq_app] using
        IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl
    have he : Spec.preimage (hU.fromSpec ≫ A.hom) ≫ f.app U =
        Spec.preimage (hV.fromSpec ≫ A.hom) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage,
        ← Category.assoc, hc, Category.assoc, (Multiplication.Construction.multiplicationMap A p).w]
    exact (congrArg CommRingCat.Hom.hom he).symm
  have : Module.Finite R B := (RingHom.finite_algebraMap).mp (f.finite_app U hU)
  have : Module.Flat R B := (RingHom.flat_algebraMap_iff).mp (by
    change (f.app U).hom.Flat
    simpa only [V, Scheme.Hom.appLE_eq_app] using f.flat_appLE hU hV le_rfl)
  have : Algebra.FinitePresentation R B := (RingHom.finitePresentation_algebraMap).mp (by
    change (f.app U).hom.FinitePresentation
    simpa only [V, Scheme.Hom.appLE_eq_app] using f.finitePresentation_appLE hU hV le_rfl)
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (f.app_injective U)
  let t : Spec Γ(A.left, U) := (⊥ : PrimeSpectrum R)
  have ht : hU.fromSpec t = genericPoint A.left := by
    change hU.fromSpec (⊥ : PrimeSpectrum R) = _
    rw [← genericPoint_eq_bot_of_affine]
    exact genericPoint_eq_of_isOpenImmersion hU.fromSpec
  have hj : hV.fromSpec ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap k B)) :=
    (Spec.map_preimage (hV.fromSpec ≫ A.hom)).symm
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ hU.fromSpec =
      hV.fromSpec ≫ (Multiplication.Construction.multiplicationMap A p).left := by
    change Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f
    simpa only [V, Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl
  have hdeg : Module.rankAtStalk (R := R) B (⊥ : PrimeSpectrum R) = p ^ (2 * g) := by
    have he := (Scheme.Hom.finrank_SpecMap_algebraMap R B (⊥ : PrimeSpectrum R)).symm
    exact (he.trans (AffineChartPullback.Construction.finrank_affine_preimage f U hU t)).trans (hdegree _)
  have hb := AffineMultiplicationBound.Construction.geometricPointCard_multiplication_chart_le_of_degree
    p A R B hU.fromSpec hV.fromSpec hj hφ g hdim hdeg t
  have hc := AffineChartPullback.Construction.geometricPointCard_affine_preimage f U hU t
  rw [ht] at hc
  have hb' : Nat.card (DefinitionsTorsion.geometricPoint A.left (genericPoint A.left) ⟶
      Over.mk (Multiplication.Construction.multiplicationMap A p).left) ≤ p ^ g := hc.symm.trans_le hb
  exact (TorsionGenericCount.Construction.torsionPointCard_le_generic_multiplication A p).trans hb'

/-- All geometric and infinitesimal steps in Openness follow from the classical
total-degree formula for multiplication on its algebraically closed fibers. -/
theorem isOpen_ordinaryLocus_of_multiplication_degree
    (p : ℕ) [Fact p.Prime]
    (hdegree : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
      (B : Over (Spec (.of k))) [GrpObj B] [IsCommMonObj B]
      [Smooth B.hom] [IsProper B.hom] [GeometricallyConnected B.hom]
      [IsFinite (DefinitionsTorsion.Construction.torsionScheme B p).hom] (g : ℕ),
      topologicalKrullDim B.left = (g : WithBot ℕ∞) →
      ∀ b : B.left, (Multiplication.Construction.multiplicationMap B p).left.finrank b = p ^ (2 * g))
    (S : Over (Spec (.of (ZMod p))))
    (A : Over S.left) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom] :
    IsOpen {s : S.left | DefinitionsTorsion.IsOrdinaryAt p A s} := by
  apply FieldReduction.Construction.isOpen_ordinaryLocus_of_finite_field_bound p _ S A
  intro k _ _ _ B _ _ _ _ _ _ g hg
  exact torsionPointCard_le_of_multiplication_degree p B g hg (hdegree k B g hg)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.DegreeReduction.Construction
