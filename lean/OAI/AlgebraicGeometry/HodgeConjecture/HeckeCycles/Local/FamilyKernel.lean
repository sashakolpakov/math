import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily

/-! # Family Kernel -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.FamilyKernel.CM.MinusFamily

/-! The global negative identity is realized by the actual local
negative identity at any single finite place. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
variable (n : ℕ)
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : MeasurableSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := borel ℚ_[OperatorFamily.CM.LocalFamily.number v]
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : BorelSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := ⟨rfl⟩

def minus (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : OperatorFamily.CM.LocalFamily.Family n := fun w =>
  if w = v then RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus ℚ_[OperatorFamily.CM.LocalFamily.number w] n (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number w)) else 1

theorem globalProjection_kernel (g : Finite.FiniteOscillator.CM.Oscillator (I := Fin n))
    (hg : Finite.FiniteOscillator.CM.projection g = 1) (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : OperatorFamily.CM.LocalFamily.globalProjection n v g = 1 := by
  change RepresentationTheory.Hecke.RadialDilation.SymplecticSwap.Realization.symplecticSwapHom (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection (OperatorFamily.CM.LocalFamily.number v)).toRingHom
    (@RepresentationTheory.Hecke.RadialDilation.PositionReindex.Realization.symplecticReindex (Fin n) (Fin n) RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf _ _ (Classical.decEq _) inferInstance _
      (Equiv.refl (Fin n)) (Finite.FiniteOscillator.CM.projection g))) = 1
  rw [hg, map_one, map_one, map_one]

theorem projection_minus (v w : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : OperatorFamily.CM.LocalFamily.localProjection n w (minus n v w) =
    OperatorFamily.CM.LocalFamily.globalProjection n w Finite.BareNe.CM.Group.minus := by
  rw [globalProjection_kernel n _ Finite.BareNe.CM.Group.project_minus]
  unfold minus
  split_ifs
  · exact RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.metaplecticMinus_projection _ _ _
  · exact map_one _

theorem operator_minus_same (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    OperatorFamily.CM.LocalFamily.operator n v (minus n v v) = LinearEquiv.neg ℂ := by
  simp only [minus, ite_true]
  exact RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_neg (OperatorFamily.CM.LocalFamily.number v) n

theorem product_away (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hv : v ∉ S) :
    OperatorFamily.CM.LocalFamily.product n S (minus n v) = 1 := by
  change S.noncommProd (fun w => OperatorFamily.CM.LocalFamily.operator n w (minus n v w))
    (fun _ _ _ _ h => OperatorFamily.CM.LocalFamily.operators_commute n h _ _) = 1
  apply (Finset.noncommProd_eq_pow_card S _ (fun _ _ _ _ h => OperatorFamily.CM.LocalFamily.operators_commute n h _ _) 1 ?_).trans (one_pow _)
  intro w hw
  have hne : w ≠ v := fun h => hv (h ▸ hw)
  simp only [minus, ite_eq_right hne, map_one]

theorem product_contains (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (hv : v ∈ S) :
    OperatorFamily.CM.LocalFamily.product n S (minus n v) = LinearEquiv.neg ℂ := by
  have he : S = insert v (S.erase v) := (Finset.insert_erase hv).symm
  rw [he]
  change Finite.CommutingProduct.CM.product _ _ (insert v (S.erase v)) _ = _
  rw [Finite.CommutingProduct.CM.product_insert _ _ _ v (Finset.notMem_erase v S)]
  change OperatorFamily.CM.LocalFamily.operator n v (minus n v v) * OperatorFamily.CM.LocalFamily.product n (S.erase v) (minus n v) = _
  rw [operator_minus_same, product_away n v _ (Finset.notMem_erase v S), mul_one]

theorem minus_realized (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : Finite.BareNe.CM.Group.minus (I := Fin n) ∈ OperatorFamily.CM.LocalFamily.realized n := by
  refine ⟨minus n v, projection_minus n v, ?_⟩
  intro f
  refine ⟨{v}, fun T hT => ?_⟩
  rw [product_contains n v T (hT (Finset.mem_singleton_self v))]
  rfl

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.FamilyKernel.CM.MinusFamily

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.FamilyKernel.CM.Family

/-! Finite products of local bare-kernel elements act by signs on the
actual global test space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.OperatorFamily.CM.LocalFamily
variable (n : ℕ)
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : MeasurableSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := borel ℚ_[OperatorFamily.CM.LocalFamily.number v]
local instance (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : BorelSpace ℚ_[OperatorFamily.CM.LocalFamily.number v] := ⟨rfl⟩

def IsSign (U : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n)) : Prop :=
  ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f, U f = ε • f

theorem sign_one : IsSign n 1 := ⟨1, one_pow _, fun f => (one_smul ℂ f).symm⟩

theorem sign_mul (U V : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Fin n))
    (hU : IsSign n U) (hV : IsSign n V) : IsSign n (U * V) := by
  obtain ⟨a, ha, hUa⟩ := hU
  obtain ⟨b, hb, hVb⟩ := hV
  refine ⟨a * b, by rw [mul_pow, ha, hb, one_mul], ?_⟩
  intro f
  change U (V f) = (a * b) • f
  rw [hUa, hVb, mul_smul]

theorem operator_kernel_sign (v : RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (u : OperatorFamily.CM.LocalFamily.Local n v) (hu : OperatorFamily.CM.LocalFamily.localProjection n v u = 1) :
    IsSign n (OperatorFamily.CM.LocalFamily.operator n v u) := by
  obtain ⟨ε, hε, hf⟩ := Schrodinger.CM.kernel_sign (OperatorFamily.CM.LocalFamily.number v) n u hu
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · have he : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[OperatorFamily.CM.LocalFamily.number v] n (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number v)) u = 1 := by
      apply LinearEquiv.ext
      intro f
      change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[OperatorFamily.CM.LocalFamily.number v] n (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number v)) u f = f
      exact (hf f).trans (one_smul ℂ f)
    change IsSign n (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom (OperatorFamily.CM.LocalFamily.number v) n _)
    rw [he, map_one]
    exact sign_one n
  · have he : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[OperatorFamily.CM.LocalFamily.number v] n (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number v)) u =
        LinearEquiv.neg ℂ := by
      apply LinearEquiv.ext
      intro f
      change RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[OperatorFamily.CM.LocalFamily.number v] n (PadicCharacter.CM.character (OperatorFamily.CM.LocalFamily.number v)) u f = -f
      exact (hf f).trans (neg_one_smul ℂ f)
    change IsSign n (RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom (OperatorFamily.CM.LocalFamily.number v) n _)
    rw [he, RepresentationTheory.Hecke.RadialDilation.PrimeTestOperators.Realization.fullPrimeOperatorHom_neg]
    exact ⟨-1, by norm_num, fun f => (neg_one_smul ℂ f).symm⟩

theorem product_kernel_sign (S : Finset RepresentationTheory.Theta.AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (u : OperatorFamily.CM.LocalFamily.Family n)
    (hu : ∀ v ∈ S, OperatorFamily.CM.LocalFamily.localProjection n v (u v) = 1) : IsSign n (OperatorFamily.CM.LocalFamily.product n S u) := by
  change IsSign n (S.noncommProd (fun v => OperatorFamily.CM.LocalFamily.operator n v (u v))
    (fun _ _ _ _ h => OperatorFamily.CM.LocalFamily.operators_commute n h _ _))
  apply Finset.noncommProd_induction
  · exact sign_mul n
  · exact sign_one n
  · intro v hv
    exact operator_kernel_sign n v (u v) (hu v hv)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Local.FamilyKernel.CM.Family

end

end OAI
