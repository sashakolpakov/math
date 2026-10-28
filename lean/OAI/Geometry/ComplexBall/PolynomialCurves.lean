import OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic
import OAI.Geometry.ComplexBall.Generation

/-! # Polynomial Curves -/

namespace OAI.Geometry.ComplexBall.PolynomialCurves.ArithmeticQuotient

noncomputable section

section

/-! Closed geometric points and the finite-center criterion for semisimplicity. -/

open scoped Classical
open OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

variable {k : Type} [Field k] {n : ℕ} (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

lemma geometricPrime_injective : Function.Injective G.geometricPrime := by
  intro g h he
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have he' := congrArg PrimeSpectrum.asIdeal he
  let p : NumberTheory.ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n (AlgebraicClosure k) :=
    MvPolynomial.X (i, j) - MvPolynomial.C (g.val i j)
  have hp : p ∈ (G.geometricPrime g).asIdeal := by
    change NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id _) g.val p = 0
    simp [p, NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  rw [he'] at hp
  change NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id _) h.val p = 0 at hp
  have hh : h.val i j - g.val i j = 0 := by simpa [p, NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix] using hp
  exact (sub_eq_zero.mp hh).symm

lemma geometricPrime_isClosed_singleton (g : G.GeometricPoints) :
    IsClosed ({G.geometricPrime g} : Set _) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by
    simp [NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]⟩)

instance geometricT1Space : @T1Space G.GeometricPoints G.geometricTopology := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  refine ⟨fun g => ?_⟩
  have he : {g} = G.geometricPrime ⁻¹' {G.geometricPrime g} := by
    ext h
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact (geometricPrime_injective G).eq_iff.symm
  rw [he]
  exact (geometricPrime_isClosed_singleton G g).preimage continuous_induced_dom

variable {K : Type*} [Field K] [CharZero K]

instance sl3CenterFinite : Finite (Subgroup.center (ArithmeticQuotientEquationsData.SL K)) := by
  let e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := K) (0 : Fin 3)
  exact Finite.of_injective e e.injective

lemma finite_solvable_normal_of_sl3_equiv {H : Type*} [Group H]
    (e : H ≃* ArithmeticQuotientEquationsData.SL K) (N : Subgroup H) (hN : N.Normal) (hsolv : Group.IsSolvable N) :
    (N : Set H).Finite := by
  let := hsolv
  let f := N.equivMapOfInjective e.toMonoidHom e.injective
  have hs : Group.IsSolvable (N.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  have hc := Generation.ArithmeticQuotient.sl3_solvable_normal_central (N.map e.toMonoidHom)
    (hN.map e.toMonoidHom e.surjective) hs
  let c : N → Subgroup.center (ArithmeticQuotientEquationsData.SL K) := fun x =>
    ⟨e x.val, hc ⟨x.val, x.property, rfl⟩⟩
  have hi : Function.Injective c := by
    intro x y h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  let : Finite N := Finite.of_injective c hi
  exact Set.toFinite _

lemma connected_solvable_normal_eq_bot_of_sl3_equiv {H : Type*} [Group H]
    [TopologicalSpace H] [T1Space H] (e : H ≃* ArithmeticQuotientEquationsData.SL K)
    (N : Subgroup H) (hN : N.Normal) (hconn : IsConnected (N : Set H))
    (hsolv : Group.IsSolvable N) : N = ⊥ := by
  have hf := finite_solvable_normal_of_sl3_equiv e N hN hsolv
  have hsub := hconn.isPreconnected.isDiscrete_iff_subsingleton.mp hf.isDiscrete
  apply bot_unique
  intro x hx
  exact Subgroup.mem_bot.mpr (hsub hx N.one_mem)

lemma semisimple_of_geometric_sl3_equiv [CharZero k]
    (e : G.GeometricPoints ≃* ArithmeticQuotientEquationsData.SL (AlgebraicClosure k)) : G.IsSemisimple := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  intro N hN _ hconn hsolv
  exact connected_solvable_normal_eq_bot_of_sl3_equiv e N hN hconn hsolv

end

/-! Polynomial curves in the actual geometric matrix points are continuous
for the Zariski topology. Curves through the identity witness connectedness. -/

open scoped Classical _root_.Polynomial
open OAI.NumberTheory.ArithmeticGroups.Lattices.Algebraic

variable {k : Type} [Field k] {n : ℕ} (G : NumberTheory.ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

lemma polynomial_zeroSet_isClosed (p : (AlgebraicClosure k)[X]) :
    IsClosed {t : CofiniteTopology (AlgebraicClosure k) |
      p.eval (CofiniteTopology.of.symm t) = 0} := by
  rw [CofiniteTopology.isClosed_iff]
  by_cases hp : p = 0
  · left
    simp [hp]
  · right
    exact (Polynomial.finite_setOfPred_isRoot hp).preimage
      CofiniteTopology.of.symm.injective.injOn

lemma polynomial_geometricPrime_continuous (γ : AlgebraicClosure k → G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (AlgebraicClosure k)[X])
    (hP : ∀ t i j, (γ t).val i j = (P i j).eval t) :
    Continuous (fun t : CofiniteTopology (AlgebraicClosure k) =>
      G.geometricPrime (γ (CofiniteTopology.of.symm t))) := by
  rw [continuous_iff_isClosed]
  intro Z hZ
  obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  have he : (fun t : CofiniteTopology (AlgebraicClosure k) =>
      G.geometricPrime (γ (CofiniteTopology.of.symm t))) ⁻¹' PrimeSpectrum.zeroLocus s =
      ⋂ p ∈ s, {t | (MvPolynomial.eval₂Hom Polynomial.C
        (fun ij => P ij.1 ij.2) p).eval (CofiniteTopology.of.symm t) = 0} := by
    ext t
    simp only [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus, Set.mem_iInter,
      Set.mem_ofPred_eq]
    apply forall_congr'
    intro p
    apply imp_congr_right
    intro _
    change NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id _) (γ _).val p = 0 ↔ _
    have hm := MvPolynomial.map_eval₂Hom
      Polynomial.C (fun ij : Fin n × Fin n => P ij.1 ij.2)
      (Polynomial.evalRingHom (CofiniteTopology.of.symm t)) p
    have hc : (Polynomial.evalRingHom (CofiniteTopology.of.symm t)).comp Polynomial.C =
        RingHom.id (AlgebraicClosure k) := by ext a; simp
    rw [hc] at hm
    simpa only [NumberTheory.ArithmeticGroups.Lattices.Algebraic.evaluateMatrix, hP, Polynomial.coe_evalRingHom] using Iff.of_eq (congrArg (fun x => x = 0) hm.symm)
  rw [he]
  exact isClosed_biInter fun p _ => polynomial_zeroSet_isClosed _

lemma polynomial_curve_continuous (γ : AlgebraicClosure k → G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (AlgebraicClosure k)[X])
    (hP : ∀ t i j, (γ t).val i j = (P i j).eval t) :
    @Continuous (CofiniteTopology (AlgebraicClosure k)) G.GeometricPoints
      inferInstance G.geometricTopology (fun t => γ (CofiniteTopology.of.symm t)) := by
  rw [continuous_induced_rng]
  exact polynomial_geometricPrime_continuous G γ P hP

lemma polynomial_curve_mem_connectedComponent [CharZero k]
    (γ : AlgebraicClosure k → G.GeometricPoints)
    (P : Matrix (Fin n) (Fin n) (AlgebraicClosure k)[X])
    (hP : ∀ t i j, (γ t).val i j = (P i j).eval t) (h0 : γ 0 = 1) (t : AlgebraicClosure k) :
    letI : TopologicalSpace G.GeometricPoints := G.geometricTopology
    γ t ∈ connectedComponent (1 : G.GeometricPoints) := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  have hc := isPreconnected_range (polynomial_curve_continuous G γ P hP)
  apply hc.subset_connectedComponent
  · exact ⟨CofiniteTopology.of 0, h0⟩
  · exact ⟨CofiniteTopology.of t, rfl⟩

lemma geometricallyConnected_of_polynomial_curves [CharZero k]
    (h : ∀ g : G.GeometricPoints, ∃ (γ : AlgebraicClosure k → G.GeometricPoints)
      (P : Matrix (Fin n) (Fin n) (AlgebraicClosure k)[X]),
      (∀ t i j, (γ t).val i j = (P i j).eval t) ∧ γ 0 = 1 ∧ γ 1 = g) :
    G.IsGeometricallyConnected := by
  let : TopologicalSpace G.GeometricPoints := G.geometricTopology
  apply connectedSpace_iff_univ.mpr
  have he : connectedComponent (1 : G.GeometricPoints) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨γ, P, hP, h0, h1⟩ := h g
    rw [← h1]
    exact polynomial_curve_mem_connectedComponent G γ P hP h0 1
  rw [← he]
  exact isConnected_connectedComponent

end

end OAI.Geometry.ComplexBall.PolynomialCurves.ArithmeticQuotient
