import OAI.AlgebraicGeometry.Crystalline.Cohomology.AdicBase
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit

/-! # Padic Frame -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrame.PadicFrameCompletion

noncomputable section

/-! # Integral module completion is the original p-power crystalline frame limit -/

universe u

variable (p : ℕ) [Fact p.Prime] (k B E : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] [CommRing E] [Algebra (WittVector p k) E]
  (r : E →+* B) (hr : Function.Surjective r)
  (hbase : r.comp (algebraMap (WittVector p k) E) =
    (algebraMap k B).comp WittVector.constantCoeff)
  (δ : DividedPowers (RingHom.ker r))
  (hδ : DividedPowers.IsDPMorphism (Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) δ
    (algebraMap (WittVector p k) E))

local notation "W" => WittVector p k
local notation "I" => Ideal.span {(p : W)}
local notation "J" => Ideal.span {(p : E)}
local notation "Tower" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicPDP.PadicPDThickening.tower p k B E r hr hbase δ hδ
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k B Tower

omit [CharP k p] in
theorem base_ideal : (I).map (algebraMap W E) = J := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

def quotientEquiv (n : ℕ) :
    (E ⧸ (I ^ n • (⊤ : Submodule W E))) ≃ₗ[W] (E ⧸ J ^ n) :=
  AdicBase.AdicBaseQuotients.quotientEquiv I J (base_ideal p k E) n

omit [CharP k p] in
theorem quotientEquiv_mk (n : ℕ) (a : E) :
    quotientEquiv p k E n (Submodule.Quotient.mk a) = Ideal.Quotient.mk (J ^ n) a :=
  AdicBase.AdicBaseQuotients.quotientEquiv_mk I J (base_ideal p k E) n a

omit [CharP k p] in
theorem quotientEquiv_symm_mk (n : ℕ) (a : E) :
    (quotientEquiv p k E n).symm (Ideal.Quotient.mk (J ^ n) a) = Submodule.Quotient.mk a :=
  (quotientEquiv p k E n).symm_apply_eq.mpr (quotientEquiv_mk p k E n a).symm

theorem transition (n m : ℕ) (h : n ≤ m)
    (x : E ⧸ (I ^ (m + 1) • (⊤ : Submodule W E))) :
    (PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom (quotientEquiv p k E (m + 1) x) =
      quotientEquiv p k E (n + 1)
        (AdicCompletion.transitionMap I E (Nat.add_le_add_right h 1) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [quotientEquiv_mk]
    exact (quotientEquiv_mk p k E (n + 1) a).symm

def toLimit : AdicCompletion I E →ₗ[W] C where
  toFun x := ⟨fun n => quotientEquiv p k E (n + 1) (x.val (n + 1)), by
    intro n m h
    exact (transition p k B E r hr hbase δ hδ n m h (x.val (m + 1))).trans
      (congrArg (quotientEquiv p k E (n + 1)) (x.property (Nat.add_le_add_right h 1)))⟩
  map_add' x y := PD.InverseLimit.PDInverseLimit.ext p k B Tower (fun n => map_add (quotientEquiv p k E (n + 1)) _ _)
  map_smul' w x := PD.InverseLimit.PDInverseLimit.ext p k B Tower
    (fun n => (quotientEquiv p k E (n + 1)).map_smul w _)

def lower (n : ℕ) : (PadicPDP.PadicPDThickening.thickening p k B E r hr hbase δ hδ n).ring →ₗ[W]
    (E ⧸ (I ^ n • (⊤ : Submodule W E))) :=
  (quotientEquiv p k E n).symm.toLinearMap.comp
    (Ideal.Quotient.factorₐ W (Ideal.pow_le_pow_right (Nat.le_succ n) : J ^ (n + 1) ≤ J ^ n)).toLinearMap

theorem lower_mk (n : ℕ) (a : E) :
    lower p k B E r hr hbase δ hδ n (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) a) =
      Submodule.Quotient.mk a := quotientEquiv_symm_mk p k E n a

theorem lower_transition (n m : ℕ) (h : n ≤ m)
    (x : (PadicPDP.PadicPDThickening.thickening p k B E r hr hbase δ hδ m).ring) :
    AdicCompletion.transitionMap I E h (lower p k B E r hr hbase δ hδ m x) =
      lower p k B E r hr hbase δ hδ n ((PD.InverseLimit.PDInverseLimit.transition p k B Tower n m h).hom x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [lower_mk]
  exact (lower_mk p k B E r hr hbase δ hδ n a).symm

def fromLimit : C →ₗ[W] AdicCompletion I E where
  toFun x := ⟨fun n => lower p k B E r hr hbase δ hδ n (x.val n), by
    intro n m h
    exact (lower_transition p k B E r hr hbase δ hδ n m h (x.val m)).trans
      (congrArg (lower p k B E r hr hbase δ hδ n) (x.property n m h))⟩
  map_add' x y := AdicCompletion.ext (fun n => map_add (lower p k B E r hr hbase δ hδ n) _ _)
  map_smul' w x := AdicCompletion.ext
    (fun n => (lower p k B E r hr hbase δ hδ n).map_smul w _)

theorem lower_quotientEquiv (n : ℕ) (x : E ⧸ (I ^ (n + 1) • (⊤ : Submodule W E))) :
    lower p k B E r hr hbase δ hδ n (quotientEquiv p k E (n + 1) x) =
      AdicCompletion.transitionMap I E (Nat.le_succ n) x := by
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    rw [quotientEquiv_mk]
    exact lower_mk p k B E r hr hbase δ hδ n a

theorem quotientEquiv_lower (n : ℕ)
    (x : (PadicPDP.PadicPDThickening.thickening p k B E r hr hbase δ hδ (n + 1)).ring) :
    quotientEquiv p k E (n + 1) (lower p k B E r hr hbase δ hδ (n + 1) x) =
      (PD.InverseLimit.PDInverseLimit.transition p k B Tower n (n + 1) (Nat.le_succ n)).hom x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [lower_mk]
  exact quotientEquiv_mk p k E (n + 1) a

def equiv : AdicCompletion I E ≃ₗ[W] C :=
  LinearEquiv.ofLinearMap (toLimit p k B E r hr hbase δ hδ) (fromLimit p k B E r hr hbase δ hδ)
    (by
      apply LinearMap.ext
      intro x
      apply PD.InverseLimit.PDInverseLimit.ext p k B Tower
      intro n
      exact (quotientEquiv_lower p k B E r hr hbase δ hδ n (x.val (n + 1))).trans
        (x.property n (n + 1) (Nat.le_succ n)))
    (by
      apply LinearMap.ext
      intro x
      apply AdicCompletion.ext
      intro n
      exact (lower_quotientEquiv p k B E r hr hbase δ hδ n (x.val (n + 1))).trans
        (x.property (Nat.le_succ n)))

theorem equiv_of (a : E) :
    equiv p k B E r hr hbase δ hδ (AdicCompletion.of I E a) =
      PD.InverseLimit.PDInverseLimit.of p k B E r hr hbase δ hδ a :=
  PD.InverseLimit.PDInverseLimit.ext p k B Tower (fun n => quotientEquiv_mk p k E (n + 1) a)

theorem eval_equiv (n : ℕ) (x : AdicCompletion I E) :
    PD.InverseLimit.PDInverseLimit.eval p k B Tower n (equiv p k B E r hr hbase δ hδ x) =
      quotientEquiv p k E (n + 1) (x.val (n + 1)) := rfl

theorem equiv_operator (D : Module.End W E) (L : Module.End W C)
    (d : ∀ n, Module.End W (PadicPDP.PadicPDThickening.thickening p k B E r hr hbase δ hδ n).ring)
    (hd : ∀ n a, d n (Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) a) =
      Ideal.Quotient.mk (PadicPDP.PadicPDThickening.ideal p E n) (D a))
    (hL : ∀ n x, PD.InverseLimit.PDInverseLimit.eval p k B Tower n (L x) =
      d n (PD.InverseLimit.PDInverseLimit.eval p k B Tower n x)) (x : AdicCompletion I E) :
    equiv p k B E r hr hbase δ hδ (AdicCompletion.map I D x) =
      L (equiv p k B E r hr hbase δ hδ x) := by
  apply PD.InverseLimit.PDInverseLimit.ext p k B Tower
  intro n
  rw [hL, eval_equiv, eval_equiv, AdicCompletion.map_val_apply]
  generalize x.val (n + 1) = z
  induction z using Submodule.Quotient.induction_on with
  | H a =>
    rw [quotientEquiv_mk]
    exact (quotientEquiv_mk p k E (n + 1) (D a)).trans (hd n a).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PadicFrame.PadicFrameCompletion
