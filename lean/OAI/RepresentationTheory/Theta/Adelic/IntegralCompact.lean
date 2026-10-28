import OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

/-! # Integral Compact -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntegralCompact

noncomputable section

/-! Compactness at almost all places of the integral matrix subgroups,
and compact open congruence levels for finite Schwartz inputs. -/

open scoped _root_.NumberField _root_.Topology
open Filter

open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.IntegralTopology OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.CompactOpen

def coefficientOrder {k : Type*} [CommRing k] (A : Subring k) (d : k) (hd : d ∈ A) :
    Subring (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) where
  carrier := {z | z.re ∈ A ∧ z.im ∈ A}
  zero_mem' := ⟨A.zero_mem, A.zero_mem⟩
  one_mem' := ⟨A.one_mem, A.zero_mem⟩
  add_mem' := fun hx hy => ⟨A.add_mem hx.1 hy.1, A.add_mem hx.2 hy.2⟩
  neg_mem' := fun hx => ⟨A.neg_mem hx.1, A.neg_mem hx.2⟩
  mul_mem' := by
    intro x y hx hy
    constructor
    · exact A.add_mem (A.mul_mem hx.1 hy.1) (A.mul_mem (A.mul_mem hd hx.2) hy.2)
    · change x.re * y.im + x.im * y.re + 0 * x.im * y.im ∈ A
      simp only [zero_mul, add_zero]
      exact A.add_mem (A.mul_mem hx.1 hy.2) (A.mul_mem hx.2 hy.1)

theorem quadraticOrder_eq_coefficientOrder
    (F : Type*) [Field F] [NumberField F] (d : F) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)
    (hd : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) :
    Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d v = coefficientOrder (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) hd := by
  apply le_antisymm
  · apply sup_le
    · rintro z ⟨a, ha, rfl⟩
      exact ⟨ha, (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem⟩
    · apply Subring.closure_le.mpr
      rintro z rfl
      exact ⟨(Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).zero_mem, (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v).one_mem⟩
  · intro z hz
    exact Weil.AdelicSplitting.Integral.Construction.quadraticOrder_of_coeff F d v z hz.1 hz.2

theorem quadraticOrder_compact
    (F : Type) [Field F] [NumberField F] (d : F) (v : FiniteSchwartz.FinitePlace F)
    (hd : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    IsCompact (Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v) : Set (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) := by
  have hO : IsCompact (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) : Set (v.adicCompletion F)) := by
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    simp only [Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
    rfl
  rw [quadraticOrder_eq_coefficientOrder F d (.inr v) hd]
  exact (SpecialUnitary.quadraticHomeomorph (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d)).isCompact_preimage.mpr (hO.prod hO)

theorem localSUIntegral_compact
    (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) (v : FiniteSchwartz.FinitePlace F)
    (hd : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) d ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)) :
    IsCompact (IntegralTopology.localSUIntegral F H (.inr v) : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v)))) := by
  let C : Set (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v))) :=
    {A | ∀ i j, A i j ∈ Weil.AdelicSplitting.Integral.Construction.quadraticOrder F d (.inr v)}
  have hC : IsCompact C :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => quadraticOrder_compact F d v hd
  have he := Units.isClosedEmbedding_embedProduct.comp
    (SpecialUnitary.specialUnitary_closed (Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v))).isClosedEmbedding_subtypeVal
  have hcp := he.isCompact_preimage (hC.prod (hC.image
    (MulOpposite.opHomeomorph : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic F d (.inr v)) ≃ₜ _).continuous))
  have heq : (IntegralTopology.localSUIntegral F H (.inr v) : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v)))) =
      (fun g : SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v)) => Units.embedProduct _ g.val) ⁻¹'
        (C ×ˢ (MulOpposite.op '' C)) := by
    ext g
    change (g.val.val ∈ C ∧ (g.val⁻¹).val ∈ C) ↔
      (g.val.val ∈ C ∧ MulOpposite.op (g.val⁻¹).val ∈ MulOpposite.op '' C)
    apply and_congr_right
    intro _
    exact MulOpposite.op_injective.mem_set_image.symm
  rw [heq]
  exact hcp

theorem localSUIntegral_eventually_compact
    (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d)) :
    ∀ᶠ v : FiniteSchwartz.FinitePlace F in cofinite,
      IsCompact (IntegralTopology.localSUIntegral F H (.inr v) : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H (.inr v)))) := by
  filter_upwards [(Sum.inr_injective.tendsto_cofinite).eventually (Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F d)] with v hv
  exact localSUIntegral_compact F H v hv

instance finiteSULocallyCompact
    (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) : LocallyCompactSpace (FiniteSchwartz.FiniteSU F H) := by
  let : Fact (∀ v : FiniteSchwartz.FinitePlace F, IsOpen
      (IntegralTopology.localSUIntegral F H.val (.inr v) : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))))) :=
    ⟨fun v => IntegralTopology.localSUIntegral_open F H.val (.inr v)⟩
  exact RestrictedProduct.locallyCompactSpace_of_group
    (B := fun v : FiniteSchwartz.FinitePlace F => IntegralTopology.localSUIntegral F H.val (.inr v))
    (fun v : FiniteSchwartz.FinitePlace F => SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v)))
    (localSUIntegral_eventually_compact F H.val)

instance finiteSUIsTopologicalGroup
    (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) : IsTopologicalGroup (FiniteSchwartz.FiniteSU F H) := by
  let : Fact (∀ v : FiniteSchwartz.FinitePlace F, IsOpen
      (IntegralTopology.localSUIntegral F H.val (.inr v) : Set (SpecialUnitary.SU (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inr v))))) :=
    ⟨fun v => IntegralTopology.localSUIntegral_open F H.val (.inr v)⟩
  infer_instance

instance finiteSUTotallyDisconnected
    (F : Type) [Field F] [NumberField F] {n : ℕ} {d : F}
    (H : (Matrix (Fin n) (Fin n) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ) : TotallyDisconnectedSpace (FiniteSchwartz.FiniteSU F H) := by
  constructor
  exact isTotallyDisconnected_of_image RestrictedProduct.continuous_coe.continuousOn
    (fun x y h => RestrictedProduct.ext _ _ (congrFun h)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end

end OAI.RepresentationTheory.Theta.Adelic.IntegralCompact
