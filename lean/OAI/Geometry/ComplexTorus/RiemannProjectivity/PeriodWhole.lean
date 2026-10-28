import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConePolynomial
import OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticCone
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ConeSurjectivityEq

/-! # Period Whole -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole.Constructions.PeriodCoordinateEquations

/-! # RiemannProjectivity: actual local monic equations for projected CM period cones -/

open Set _root_.Polynomial _root_.Metric

def HasLocalMonicEquation {d : ℕ} (S : Set ((Fin d → ℂ) × ℂ))
    (x : Fin d → ℂ) (z₀ : ℂ) : Prop :=
  ∃ (R : ℝ) (k : ℕ) (U : Set (Fin d → ℂ))
      (P : (Fin d → ℂ) → ℂ[X]) (c : (Fin d → ℂ) → ℂ),
    0 < R ∧ IsOpen U ∧ x ∈ U ∧ DifferentiableOn ℂ c U ∧
    U ⊆ closure {y | y ∈ U ∧ c y ≠ 0} ∧
    (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
    (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
    (∀ y ∈ U, ∀ z, (P y).eval z = 0 → (y, z) ∈ S) ∧
    (∀ y ∈ U, c y ≠ 0 → (P y).Separable) ∧
    ∀ y ∈ U, ∀ z ∈ ball z₀ R, (y, z) ∈ S ↔ (P y).eval z = 0

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem period_coordinate_equations (hRiemannProjectivity : RiemannProjectivity.Fin.Constructions.RiemannProjectivityInput) (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    ∃ (n : ℕ) (f : Φ.periodTorus → Projectivization ℂ (Fin (n + 1) → ℂ))
      (L : (Fin (n + 1) → ℂ) →L[ℂ]
        (Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ)),
      Topology.IsClosedEmbedding f ∧
      IsProperMap (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      Function.Surjective (fun v : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) => L v) ∧
      (∀ y, {v : Fin (n + 1) → ℂ | v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) ∧ L v = y}.Finite) ∧
      ∀ l : (Fin (n + 1) → ℂ) →L[ℂ] ℂ, Function.Surjective (L.prod l) →
        ∀ (x : Fin (Module.finrank ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) + 1) → ℂ) (z₀ : ℂ),
          (x, z₀) ∈ (fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f) → x ≠ 0 →
          HasLocalMonicEquation ((fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) x z₀ := by
  obtain ⟨n, f, L, hf, hd, hker, hp, hi⟩ :=
    RegularConeOf.Constructions.RegularCone.proper_period_cone_projection_with_interior_and_immersions hRiemannProjectivity Φ
  have hclosed := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.isClosed_projectiveCone (range f) hf.isClosed_range
  have hcone := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.smul_mem_projectiveCone (range f)
  have hlocal := FiniteCone.Constructions.FiniteConeFibers.cone_holomorphic_of_period_embedding Φ f hf hd
  have hfinite := FiniteCone.Constructions.FiniteConeFibers.finite_proper_cone_fiber L hp hker hlocal
  refine ⟨n, f, L, hf, hp,
    ConeSurjectivityEq.Constructions.ConeSurjectivity.surjective_cone_projection L hclosed hcone hker hlocal hi,
    hfinite, ?_⟩
  intro l hl x z₀ hx hx0
  have hpairker : ∀ v ∈ AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f), (L.prod l) v = 0 → v = 0 := by
    intro v hv hzero
    exact hker v hv (congrArg Prod.fst hzero)
  have hpairproper := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Projection.Constructions.Cone.isProperMap_projection hclosed hcone (L.prod l) hpairker
  have hpairclosed : IsClosed ((fun v => (L v, l v)) '' AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveCone.Constructions.Cone.projectiveCone (range f)) := by
    have h := hpairproper.isClosedMap.isClosed_range
    convert! h using 1
    ext u
    exact ⟨fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩,
      fun ⟨v, he⟩ => ⟨v, v.property, he⟩⟩
  have hpairlocal := AnalyticCone.Constructions.AnalyticConeImage.linear_projection (L.prod l) hl hclosed hcone
    hpairker hlocal (x, z₀) hx (fun hzero => hx0 (congrArg Prod.fst hzero))
  exact ConePolynomial.Constructions.ConePolynomialEquations.local_equation_of_coordinate_image Φ f hf.isEmbedding
    (fun z i hi => (hd z i hi).1) L hfinite l hpairclosed hx0 hpairlocal

end Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole.Constructions.PeriodCoordinateEquations

namespace Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole.Constructions.WholeFiberPolynomial

/-!
# RiemannProjectivity: one holomorphic monic polynomial for a whole finite fiber

Properness confines nearby fibers to finitely many local equation disks.
The product of their equations describes the entire fiber; overlaps may
create repeated roots, to be removed by the separate squarefree construction.
-/

open Set _root_.Polynomial _root_.Metric
open scoped BigOperators
open OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole.Constructions.PeriodCoordinateEquations

theorem exists_polynomial {d : ℕ} {S : Set ((Fin d → ℂ) × ℂ)} {x : Fin d → ℂ}
    (hproper : IsProperMap (fun p : S => p.val.1))
    (hfinite : {z : ℂ | (x, z) ∈ S}.Finite)
    (hlocal : ∀ z, (x, z) ∈ S → PeriodCoordinateEquations.HasLocalMonicEquation S x z) :
    ∃ (k : ℕ) (U : Set (Fin d → ℂ)) (P : (Fin d → ℂ) → ℂ[X]),
      IsOpen U ∧ x ∈ U ∧
      (∀ j, DifferentiableOn ℂ (fun y => (P y).coeff j) U) ∧
      (∀ y, (P y).Monic ∧ (P y).natDegree = k) ∧
      ∀ y ∈ U, ∀ z, (y, z) ∈ S ↔ (P y).eval z = 0 := by
  classical
  let K := {z : ℂ | (x, z) ∈ S}
  let : Fintype K := hfinite.fintype
  choose R k U Q c hR hU hxU hc hdense hcoeff hQ hroot hsep heq using
    (fun a : K => hlocal a a.property)
  let O : Set ((Fin d → ℂ) × ℂ) := ⋃ a : K, Prod.snd ⁻¹' ball (a : ℂ) (R a)
  have hO : IsOpen O := isOpen_iUnion (fun a => isOpen_ball.preimage continuous_snd)
  let B : Set S := Subtype.val ⁻¹' Oᶜ
  have hB : IsClosed B := hO.isClosed_compl.preimage continuous_subtype_val
  let bad := (fun p : S => p.val.1) '' B
  have hbad : IsClosed bad := hproper.isClosedMap B hB
  have hxnot : x ∉ bad := by
    rintro ⟨⟨⟨y, z⟩, hyz⟩, hpB, hpx⟩
    dsimp only at hpx
    subst y
    exact hpB (mem_iUnion.mpr ⟨⟨z, hyz⟩, mem_ball_self (hR ⟨z, hyz⟩)⟩)
  let W := badᶜ ∩ ⋂ a : K, U a
  have hWa (a : K) : W ⊆ U a := fun _ hy => mem_iInter.mp hy.2 a
  let P : (Fin d → ℂ) → ℂ[X] := fun y => ∏ a : K, Q a y
  refine ⟨∑ a : K, k a, W, P, hbad.isOpen_compl.inter (isOpen_iInter_of_finite hU),
    ⟨hxnot, mem_iInter.mpr hxU⟩,
    fun j => BranchCoefficientsAt.Constructions.BranchCoefficients.differentiableOn_coeff_prod Q
      (fun a j => (hcoeff a j).mono (hWa a)) j, ?_, ?_⟩
  · intro y
    refine ⟨monic_prod_of_monic _ _ (fun a _ => (hQ a y).1), ?_⟩
    change (∏ a : K, Q a y).natDegree = ∑ a : K, k a
    rw [natDegree_prod_of_monic _ _ (fun a _ => (hQ a y).1)]
    exact Finset.sum_congr rfl (fun a _ => (hQ a y).2)
  · intro y hy z
    change (y, z) ∈ S ↔ (∏ a : K, Q a y).eval z = 0
    rw [eval_prod, Finset.prod_eq_zero_iff]
    constructor
    · intro hyz
      have hyo : (y, z) ∈ O := by
        by_contra hnot
        exact hy.1 ⟨⟨(y, z), hyz⟩, hnot, rfl⟩
      obtain ⟨a, ha⟩ := mem_iUnion.mp hyo
      exact ⟨a, Finset.mem_univ _, (heq a y (hWa a hy) z ha).mp hyz⟩
    · rintro ⟨a, _, ha⟩
      exact hroot a y (hWa a hy) z ha

end Geometry.ComplexTorus.RiemannProjectivity.PeriodWhole.Constructions.WholeFiberPolynomial

end

end OAI
