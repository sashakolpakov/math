import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SquareZero
import Mathlib.RingTheory.Derivation.Basic

/-! # Envelope Derivations DP -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeDerivationsDP.EnvelopeDerivations

noncomputable section

/-!
# Extending derivations across a relative divided-power envelope

The graph of a derivation is a ring map to a square-zero extension.
The envelope's universal property lifts this graph; its second component
is the desired divided-power derivation.
-/

open TrivSqZeroExt

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal A)
  (hbase : I₀.map (algebraMap R A) ≤ I)

local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

variable (M : Type u) [AddCommGroup M]
  [Module (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M] [Module A M]
  [Module R M] [IsScalarTower A (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M]
  [Module (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)ᵐᵒᵖ M]
  [IsCentralScalar (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M]
  (d : Derivation R A M)

/-- The graph of a derivation, with first component the envelope map. -/
def graph : A →+* TrivSqZeroExt E M where
  toFun a := (algebraMap A E a, d a)
  map_one' := TrivSqZeroExt.ext (map_one _) d.map_one_eq_zero
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero d)
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (map_add d a b)
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ a b
    · change d (a * b) = algebraMap A E a • d b +
        MulOpposite.op (algebraMap A E b) • d a
      simp only [op_smul_eq_smul, Derivation.leibniz, algebraMap_smul]

theorem graph_base :
    (graph R A I₀ δ₀ I M d).comp (algebraMap R A) =
      (inlHom E M).comp ((algebraMap A E).comp (algebraMap R A)) := by
  ext r : 1
  apply TrivSqZeroExt.ext
  · rfl
  · exact d.map_algebraMap r

/-- The square-zero target for the graph, carrying the explicit PD structure. -/
def target : PD.EnvelopeDp.PDEnvelope.Target R A I₀ δ₀ I where
  ring := CommRingCat.of (TrivSqZeroExt E M)
  algebra := (graph R A I₀ δ₀ I M d).toAlgebra
  ideal := SquareZero.SquareZeroDividedPowers.ideal (M := M) J
  dp := SquareZero.SquareZeroDividedPowers.dividedPowers δ
  contains := Ideal.map_le_iff_le_comap.mpr (fun a ha =>
    PD.EnvelopeDp.PDEnvelope.contains R A I₀ δ₀ I (Ideal.mem_map_of_mem _ ha))
  baseDP := by
    change DividedPowers.IsDPMorphism δ₀ (SquareZero.SquareZeroDividedPowers.dividedPowers δ)
      ((graph R A I₀ δ₀ I M d).comp (algebraMap R A))
    rw [graph_base]
    exact DividedPowers.IsDPMorphism.comp _
      (SquareZero.SquareZeroDividedPowers.inl_isDPMorphism (M := M) δ)
      (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R A I₀ δ₀ I hbase)

/-- The graph lifted to the envelope. -/
def liftedGraph : E →+* TrivSqZeroExt E M :=
  PD.EnvelopeDp.PDEnvelope.evaluate R A I₀ δ₀ I (target R A I₀ δ₀ I hbase M d)

@[simp] theorem liftedGraph_algebraMap (a : A) :
    liftedGraph R A I₀ δ₀ I hbase M d (algebraMap A E a) =
      (algebraMap A E a, d a) := rfl

def firstComponent : E →ₐ[A] E where
  __ := (fstHom E E M).toRingHom.comp (liftedGraph R A I₀ δ₀ I hbase M d)
  commutes' _ := rfl

theorem firstComponent_isDPMorphism :
    DividedPowers.IsDPMorphism δ δ
      (firstComponent R A I₀ δ₀ I hbase M d).toRingHom :=
  DividedPowers.IsDPMorphism.comp _
    (SquareZero.SquareZeroDividedPowers.fst_isDPMorphism (M := M) δ)
    (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A I₀ δ₀ I (target R A I₀ δ₀ I hbase M d))

theorem firstComponent_eq_id :
    firstComponent R A I₀ δ₀ I hbase M d = AlgHom.id A E := by
  let T := PD.EnvelopeDp.PDEnvelope.envelopeTarget R A I₀ δ₀ I hbase
  exact (PD.EnvelopeDp.PDEnvelope.lift_unique R A I₀ δ₀ I T _
    (firstComponent_isDPMorphism R A I₀ δ₀ I hbase M d)).trans
    (PD.EnvelopeDp.PDEnvelope.lift_unique R A I₀ δ₀ I T (AlgHom.id A E)
      (DividedPowers.DPMorphism.id δ).isDPMorphism).symm

@[simp] theorem liftedGraph_fst (x : E) :
    (liftedGraph R A I₀ δ₀ I hbase M d x).fst = x :=
  DFunLike.congr_fun (firstComponent_eq_id R A I₀ δ₀ I hbase M d) x

variable [Algebra R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)]
  [IsScalarTower R A (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)]
  [IsScalarTower R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M]

omit [IsScalarTower R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M] in
theorem liftedGraph_base (r : R) :
    liftedGraph R A I₀ δ₀ I hbase M d (algebraMap R E r) =
      inl (algebraMap R E r) := by
  rw [IsScalarTower.algebraMap_apply R A E, liftedGraph_algebraMap]
  apply TrivSqZeroExt.ext
  · rfl
  · exact d.map_algebraMap r

/-- The derivation obtained as the second component of the lifted graph. -/
def extend : Derivation R E M where
  toFun x := (liftedGraph R A I₀ δ₀ I hbase M d x).snd
  map_add' x y := congrArg TrivSqZeroExt.snd
    (map_add (liftedGraph R A I₀ δ₀ I hbase M d) x y)
  map_smul' r x := by
    change (liftedGraph R A I₀ δ₀ I hbase M d (r • x)).snd = _
    rw [Algebra.smul_def, map_mul, liftedGraph_base]
    change algebraMap R E r • (liftedGraph R A I₀ δ₀ I hbase M d x).snd +
      MulOpposite.op (liftedGraph R A I₀ δ₀ I hbase M d x).fst • (0 : M) = _
    simp only [smul_zero, add_zero, algebraMap_smul, RingHom.id_apply]
  map_one_eq_zero' := congrArg TrivSqZeroExt.snd
    (map_one (liftedGraph R A I₀ δ₀ I hbase M d))
  leibniz' x y := by
    change (liftedGraph R A I₀ δ₀ I hbase M d (x * y)).snd =
      x • (liftedGraph R A I₀ δ₀ I hbase M d y).snd +
      y • (liftedGraph R A I₀ δ₀ I hbase M d x).snd
    rw [map_mul]
    simp only [snd_mul, liftedGraph_fst, op_smul_eq_smul]

@[simp] theorem extend_algebraMap (a : A) :
    extend R A I₀ δ₀ I hbase M d (algebraMap A E a) = d a := rfl

theorem extend_dpow (n : ℕ) {x : E} (hx : x ∈ J) :
    extend R A I₀ δ₀ I hbase M d ((δ).dpow (n + 1) x) =
      (δ).dpow n x • extend R A I₀ δ₀ I hbase M d x := by
  have hd : liftedGraph R A I₀ δ₀ I hbase M d ((δ).dpow (n + 1) x) =
      (SquareZero.SquareZeroDividedPowers.dividedPowers δ).dpow (n + 1)
        (liftedGraph R A I₀ δ₀ I hbase M d x) :=
    (PD.EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A I₀ δ₀ I
      (target R A I₀ δ₀ I hbase M d)).map_dpow hx
  change (liftedGraph R A I₀ δ₀ I hbase M d ((δ).dpow (n + 1) x)).snd = _
  rw [hd, SquareZero.SquareZeroDividedPowers.dividedPowers_snd δ n
    (by simpa only [liftedGraph_fst] using hx), liftedGraph_fst]
  rfl

variable (D : Derivation R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M)
  (hc : ∀ a, D (algebraMap A (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) a) = d a)

/-- Any extension has a graph as an algebra map to the same square-zero target. -/
def extensionGraph : E →ₐ[A] (target R A I₀ δ₀ I hbase M d).ring where
  toFun x := ((x, D x) : TrivSqZeroExt E M)
  map_one' := TrivSqZeroExt.ext (R := E) (M := M) rfl D.map_one_eq_zero
  map_zero' := TrivSqZeroExt.ext (R := E) (M := M) rfl (map_zero D)
  map_add' x y := TrivSqZeroExt.ext (R := E) (M := M) rfl (map_add D x y)
  map_mul' x y := by
    apply TrivSqZeroExt.ext (R := E) (M := M)
    · rfl
    · change D (x * y) = x • D y + MulOpposite.op y • D x
      rw [D.leibniz, op_smul_eq_smul]
  commutes' a := TrivSqZeroExt.ext rfl (hc a)

omit [IsScalarTower R A (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I)]
  [IsScalarTower R (PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I) M] in
theorem extensionGraph_isDPMorphism
    (hD : ∀ n x, x ∈ J → D ((δ).dpow (n + 1) x) = (δ).dpow n x • D x) :
    DividedPowers.IsDPMorphism δ (target R A I₀ δ₀ I hbase M d).dp
      (extensionGraph R A I₀ δ₀ I hbase M d D hc).toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => hx)
  dpow_comp {n} x hx := by
    change SquareZero.SquareZeroDividedPowers.dpow δ n (x, D x) = ((δ).dpow n x, D ((δ).dpow n x))
    rw [SquareZero.SquareZeroDividedPowers.dpow_of_mem δ n (x := (x, D x)) hx]
    apply TrivSqZeroExt.ext
    · exact SquareZero.SquareZeroDividedPowers.operation_fst δ n (x, D x)
    · cases n with
      | zero =>
        change 0 = D ((δ).dpow 0 x)
        rw [(δ).dpow_zero hx, D.map_one_eq_zero]
      | succ n => exact (hD n x hx).symm

include hc in
theorem extend_unique
    (hD : ∀ n x, x ∈ J → D ((δ).dpow (n + 1) x) = (δ).dpow n x • D x) :
    D = extend R A I₀ δ₀ I hbase M d := by
  have h := PD.EnvelopeDp.PDEnvelope.lift_unique R A I₀ δ₀ I
    (target R A I₀ δ₀ I hbase M d) (extensionGraph R A I₀ δ₀ I hbase M d D hc)
    (extensionGraph_isDPMorphism R A I₀ δ₀ I hbase M d D hc hD)
  apply Derivation.ext
  intro x
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun h x)

include hbase in
/-- Every derivation extends uniquely as a divided-power derivation. -/
theorem existsUnique_extend :
    ∃! D : Derivation R E M,
      (∀ a, D (algebraMap A E a) = d a) ∧
      (∀ n x, x ∈ J → D ((δ).dpow (n + 1) x) = (δ).dpow n x • D x) := by
  refine ⟨extend R A I₀ δ₀ I hbase M d, ⟨?_, ?_⟩, ?_⟩
  · exact extend_algebraMap R A I₀ δ₀ I hbase M d
  · intro n x hx
    exact extend_dpow R A I₀ δ₀ I hbase M d n hx
  · intro D hD
    exact extend_unique R A I₀ δ₀ I hbase M d D hD.1 hD.2

include hbase in
/-- Two PD derivations agree when they agree on the original algebra. -/
theorem derivation_ext (D₁ D₂ : Derivation R E M)
    (hc : ∀ a, D₁ (algebraMap A E a) = D₂ (algebraMap A E a))
    (h₁ : ∀ n x, x ∈ J → D₁ ((δ).dpow (n + 1) x) = (δ).dpow n x • D₁ x)
    (h₂ : ∀ n x, x ∈ J → D₂ ((δ).dpow (n + 1) x) = (δ).dpow n x • D₂ x) :
    D₁ = D₂ :=
  (extend_unique R A I₀ δ₀ I hbase M (D₂.compAlgebraMap A) D₁ hc h₁).trans
    (extend_unique R A I₀ δ₀ I hbase M (D₂.compAlgebraMap A) D₂ (fun _ => rfl) h₂).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeDerivationsDP.EnvelopeDerivations
