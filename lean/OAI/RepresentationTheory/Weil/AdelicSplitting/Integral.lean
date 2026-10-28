import OAI.RepresentationTheory.Weil.AdelicSplitting.Characters
import OAI.RepresentationTheory.Weil.AdelicSplitting.CentralProduct

/-! # Integral -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction

noncomputable section

/-! Integral orders, actual restricted unitary groups, and rational diagonal
maps. The order O_v[δ] suffices: finitely many nonmaximal or ramified orders
do not change the underlying restricted-product group. -/

open scoped _root_.NumberField Classical
open Filter IsDedekindDomain

section Matrices
variable {R G I : Type*} [CommRing R] [Group G] [Fintype I] [DecidableEq I]

def integralMatrixGroup (ρ : G →* Matrix I I R) (S : Subring R) : Subgroup G where
  carrier := {g | (∀ i j, ρ g i j ∈ S) ∧ ∀ i j, ρ g⁻¹ i j ∈ S}
  one_mem' := by
    constructor <;> intro i j <;> by_cases h : i = j <;> simp [h]
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro i j
      rw [map_mul, Matrix.mul_apply]
      exact S.sum_mem fun t _ => S.mul_mem (hg.1 i t) (hh.1 t j)
    · intro i j
      rw [mul_inv_rev, map_mul, Matrix.mul_apply]
      exact S.sum_mem fun t _ => S.mul_mem (hh.2 i t) (hg.2 t j)
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

end Matrices

variable (F : Type*) [Field F] [NumberField F]

def localIntegerRing : (v : ArchimedeanAdeles.Construction.Places F) → Subring (ArchimedeanAdeles.Construction.Completion F v)
  | Sum.inl _ => ⊤
  | Sum.inr v => (v.adicCompletionIntegers F).toSubring

def quadraticGenerator {R : Type*} [CommRing R] (d : R) : UnitaryBase.Construction.Quadratic R d := ⟨0, 1⟩

def quadraticOrder (d : F) (v : ArchimedeanAdeles.Construction.Places F) : Subring (ArchimedeanAdeles.Construction.localQuadratic F d v) :=
  (localIntegerRing F v).map (algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v)) ⊔
    Subring.closure {quadraticGenerator (ArchimedeanAdeles.Construction.rationalScalar F v d)}

theorem quadraticOrder_of_coeff (d : F) (v : ArchimedeanAdeles.Construction.Places F) (z : ArchimedeanAdeles.Construction.localQuadratic F d v)
    (hr : z.re ∈ localIntegerRing F v) (hi : z.im ∈ localIntegerRing F v) :
    z ∈ quadraticOrder F d v := by
  have hs (a : ArchimedeanAdeles.Construction.Completion F v) (ha : a ∈ localIntegerRing F v) :
      algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v) a ∈ quadraticOrder F d v := by
    have hle : (localIntegerRing F v).map
        (algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v)) ≤ quadraticOrder F d v := le_sup_left
    exact hle (Subring.mem_map.mpr ⟨a, ha, rfl⟩)
  have hd : quadraticGenerator (ArchimedeanAdeles.Construction.rationalScalar F v d) ∈ quadraticOrder F d v := by
    have hle : Subring.closure {quadraticGenerator (ArchimedeanAdeles.Construction.rationalScalar F v d)} ≤
        quadraticOrder F d v := le_sup_right
    exact hle (Subring.subset_closure (Set.mem_singleton _))
  have hz : z = algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v) z.re +
      algebraMap (ArchimedeanAdeles.Construction.Completion F v) (ArchimedeanAdeles.Construction.localQuadratic F d v) z.im *
        quadraticGenerator (ArchimedeanAdeles.Construction.rationalScalar F v d) := by
    apply QuadraticAlgebra.ext <;>
      simp [quadraticGenerator, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  rw [hz]
  exact (quadraticOrder F d v).add_mem (hs z.re hr)
    ((quadraticOrder F d v).mul_mem (hs z.im hi) hd)

theorem rationalScalar_integral (a : F) :
    ∀ᶠ v in cofinite, ArchimedeanAdeles.Construction.rationalScalar F v a ∈ localIntegerRing F v := by
  have h := (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) a).property
  rw [Filter.eventually_cofinite] at h ⊢
  apply (h.image (Sum.inr : HeightOneSpectrum (𝓞 F) → ArchimedeanAdeles.Construction.Places F)).subset
  intro v hv
  cases v with
  | inl w => exact False.elim (hv (Subring.mem_top _))
  | inr w => exact ⟨w, hv, rfl⟩

def rationalQuadraticLocal (d : F) (v : ArchimedeanAdeles.Construction.Places F) : UnitaryBase.Construction.Quadratic F d →+* ArchimedeanAdeles.Construction.localQuadratic F d v :=
  UnitaryBase.Construction.quadraticBaseChange (ArchimedeanAdeles.Construction.rationalScalar F v) d

theorem rationalQuadraticLocal_integral (d : F) (z : UnitaryBase.Construction.Quadratic F d) :
    ∀ᶠ v in cofinite, rationalQuadraticLocal F d v z ∈ quadraticOrder F d v := by
  filter_upwards [rationalScalar_integral F z.re, rationalScalar_integral F z.im] with v hr hi
  exact quadraticOrder_of_coeff F d v _ hr hi

variable {n : ℕ} {d : F} (H : Matrix (Fin n) (Fin n) (UnitaryBase.Construction.Quadratic F d))

abbrev localizedForm (v : ArchimedeanAdeles.Construction.Places F) := H.map (rationalQuadraticLocal F d v)
abbrev LocalUnitary (v : ArchimedeanAdeles.Construction.Places F) := UnitaryBase.Construction.Unitary (localizedForm F H v)

def localUnitaryIntegral (v : ArchimedeanAdeles.Construction.Places F) : Subgroup (LocalUnitary F H v) :=
  integralMatrixGroup
    ((Units.coeHom _).comp (UnitaryBase.Construction.unitaryMatrix (localizedForm F H v))) (quadraticOrder F d v)

def rationalUnitaryLocal (v : ArchimedeanAdeles.Construction.Places F) : UnitaryBase.Construction.Unitary H →* LocalUnitary F H v :=
  UnitaryBase.Construction.unitaryBaseChange (rationalQuadraticLocal F d v)
    (UnitaryBase.Construction.quadraticBaseChange_star (ArchimedeanAdeles.Construction.rationalScalar F v) d) H

theorem rationalUnitaryLocal_integral (g : UnitaryBase.Construction.Unitary H) :
    ∀ᶠ v in cofinite, rationalUnitaryLocal F H v g ∈ localUnitaryIntegral F H v := by
  have hv : ∀ᶠ v in cofinite, ∀ i j,
      rationalQuadraticLocal F d v (g.val.val i j) ∈ quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      rationalQuadraticLocal_integral F d (g.val.val i j)
  have hi : ∀ᶠ v in cofinite, ∀ i j,
      rationalQuadraticLocal F d v ((g⁻¹).val.val i j) ∈ quadraticOrder F d v :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      rationalQuadraticLocal_integral F d ((g⁻¹).val.val i j)
  filter_upwards [hv, hi] with v hv hi
  refine ⟨hv, ?_⟩
  intro i j
  change ((rationalUnitaryLocal F H v g)⁻¹).val.val i j ∈ quadraticOrder F d v
  rw [← map_inv]
  exact hi i j

abbrev AdelicUnitary := RestrictedLimits.Construction.RestrictedGroup (localUnitaryIntegral F H)

def rationalUnitary : UnitaryBase.Construction.Unitary H →* AdelicUnitary F H :=
  RestrictedLimits.Construction.diagonalMap (localUnitaryIntegral F H) (rationalUnitaryLocal F H)
    (rationalUnitaryLocal_integral F H)

@[simp] theorem rationalUnitary_apply (g : UnitaryBase.Construction.Unitary H) (v : ArchimedeanAdeles.Construction.Places F) :
    rationalUnitary F H g v = rationalUnitaryLocal F H v g := rfl

variable {m : ℕ} (K : Matrix (Fin m) (Fin m) (UnitaryBase.Construction.Quadratic F d))

def localPairIntegral (v : ArchimedeanAdeles.Construction.Places F) :
    Subgroup (LocalUnitary F H v × LocalUnitary F K v) :=
  (localUnitaryIntegral F H v).prod (localUnitaryIntegral F K v)

abbrev AdelicDualPair := RestrictedLimits.Construction.RestrictedGroup (localPairIntegral F H K)

def rationalPairLocal (v : ArchimedeanAdeles.Construction.Places F) :
    UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K →* LocalUnitary F H v × LocalUnitary F K v :=
  (rationalUnitaryLocal F H v).prodMap (rationalUnitaryLocal F K v)

theorem rationalPairLocal_integral (g : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K) :
    ∀ᶠ v in cofinite, rationalPairLocal F H K v g ∈ localPairIntegral F H K v := by
  filter_upwards [rationalUnitaryLocal_integral F H g.1,
    rationalUnitaryLocal_integral F K g.2] with v h₁ h₂
  exact ⟨h₁, h₂⟩

def rationalPair : UnitaryBase.Construction.Unitary H × UnitaryBase.Construction.Unitary K →* AdelicDualPair F H K :=
  RestrictedLimits.Construction.diagonalMap (localPairIntegral F H K) (rationalPairLocal F H K)
    (rationalPairLocal_integral F H K)

def includeUnitaryPlace (v : ArchimedeanAdeles.Construction.Places F) :
    LocalUnitary F H v × LocalUnitary F K v →ₜ* AdelicDualPair F H K :=
  RestrictedLimits.Construction.includePlaceContinuous (localPairIntegral F H K) v

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Integral.Construction
