import OAI.RepresentationTheory.Theta.Adelic.CompactOpen
import OAI.RepresentationTheory.Theta.Adelic.RestrictedSmoothness
import OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology

/-! # Special Unitary -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! The determinant-one subgroup of the actual quadratic-algebra unitary
group, with its usual local topology. At finite places it has compact open
subgroups and the restricted oscillator action is smooth. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction
open OAI.RepresentationTheory.Theta.Adelic.CompactOpen OAI.RepresentationTheory.Theta.Adelic.RestrictedSmoothness
open scoped _root_.Topology

def quadraticHomeomorph {k : Type*} [CommRing k] [TopologicalSpace k] (d : k) :
    Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃ₜ k × k where
  toEquiv := QuadraticAlgebra.equivProd d 0
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous ((QuadraticAlgebra.equivProd d 0) ∘
      (QuadraticAlgebra.equivProd d 0).symm)
    simpa only [Equiv.self_comp_symm] using (continuous_id : Continuous (id : k × k → k × k))

instance quadraticT2 {k : Type*} [CommRing k] [TopologicalSpace k] [T2Space k] (d : k) :
    T2Space (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) := (quadraticHomeomorph d).symm.t2Space

instance quadraticLocallyCompact {k : Type*} [CommRing k] [TopologicalSpace k]
    [LocallyCompactSpace k] (d : k) : LocallyCompactSpace (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :=
  (quadraticHomeomorph d).isClosedEmbedding.locallyCompactSpace

instance quadraticTotallyDisconnected {k : Type*} [CommRing k] [TopologicalSpace k]
    [TotallyDisconnectedSpace k] (d : k) : TotallyDisconnectedSpace (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :=
  (quadraticHomeomorph d).symm.totallyDisconnectedSpace

variable {R : Type*} [CommRing R] [StarRing R]
    {n : Type*} [Fintype n] [DecidableEq n]

def specialUnitary (H : Matrix n n R) : Subgroup (Matrix n n R)ˣ :=
  Weil.AdelicSplitting.UnitaryBase.Construction.unitaryIsometries H ⊓ (Matrix.GeneralLinearGroup.det : (Matrix n n R)ˣ →* Rˣ).ker

abbrev SU (H : Matrix n n R) := specialUnitary H

def includeUnitary (H : Matrix n n R) : SU H →* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H :=
  Subgroup.inclusion inf_le_left

variable [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R] [T2Space R]

theorem specialUnitary_closed (H : Matrix n n R) :
    IsClosed (specialUnitary H : Set (Matrix n n R)ˣ) := by
  have hform : IsClosed {g : (Matrix n n R)ˣ | g.val.conjTranspose * H * g.val = H} :=
    isClosed_eq (by fun_prop) continuous_const
  have hdet : IsClosed {g : (Matrix n n R)ˣ | g.val.det = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  convert hform.inter hdet using 1
  ext g
  change (_ ∧ Matrix.GeneralLinearGroup.det g = 1) ↔ (_ ∧ g.val.det = 1)
  exact and_congr_right (fun _ => Units.ext_iff)

instance specialUnitaryLocallyCompact [LocallyCompactSpace R] (H : Matrix n n R) :
    LocallyCompactSpace (SU H) := by
  let : LocallyCompactSpace (Matrix n n R) := inferInstanceAs (LocallyCompactSpace (n → n → R))
  exact (specialUnitary_closed H).isClosedEmbedding_subtypeVal.locallyCompactSpace

def includeUnitaryContinuous (H : Matrix n n R) : SU H →ₜ* Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H :=
  ⟨includeUnitary H, continuous_subtype_val.subtype_mk _⟩

instance specialUnitaryTotallyDisconnected
    [TotallyDisconnectedSpace R] (H : Matrix n n R) : TotallyDisconnectedSpace (SU H) := by
  let : TotallyDisconnectedSpace (Matrix n n R) :=
    inferInstanceAs (TotallyDisconnectedSpace (n → n → R))
  let : TotallyDisconnectedSpace (Matrix n n R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.totallyDisconnectedSpace
  let : TotallyDisconnectedSpace (Matrix n n R)ˣ :=
    Units.isEmbedding_embedProduct.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  infer_instance

instance specialUnitaryNonarchimedean [LocallyCompactSpace R]
    [TotallyDisconnectedSpace R] (H : Matrix n n R) : NonarchimedeanGroup (SU H) :=
  CompactOpen.nonarchimedean_of_locallyCompact_totallyDisconnected

variable {k : Type} [NormedField k] [IsUltrametricDist k] [CharZero k]
    [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] [CompleteSpace k] {N : ℕ}
    (d : k) (H : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))
    (ψ : AddChar k ℂ) (hc : Continuous (fun t : k => ψ t))
    (hu : ∀ t : k, ‖ψ t‖ = 1)

include hc hu in
theorem specialUnitary_action_smooth
    (hk : ¬ DiscreteTopology k) (hn : ∃ t : k, ψ t ≠ 1)
    (s : Weil.AdelicSplitting.UnitaryBase.Construction.Unitary H →ₜ* Weil.AdelicSplitting.Oscillator.Construction.LocalCover k N ψ) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat k N) :
    IsOpen {g : SU H | Weil.AdelicSplitting.Oscillator.Construction.localOperator k N ψ (s (includeUnitary H g)) f = f} := by
  exact RestrictedSmoothness.restricted_action_smooth ψ hc hu hk hn
    (s.comp (includeUnitaryContinuous H)) f

end RepresentationTheory.Theta.Adelic.SpecialUnitary

namespace RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

/-! Explicit root coordinates on a split quadratic algebra. These are the
algebraic starting point for constructing stable split polarizations. -/

open OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticTopology.Construction

variable {k : Type*} [Field k] [CharZero k] {d : k}
    (r : k) (hr : r ^ 2 = d) (hr0 : r ≠ 0)

def splitAlgebra : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d ≃ₐ[k] k × k where
  toFun z := (z.re + r * z.im, z.re - r * z.im)
  invFun p := ⟨(p.1 + p.2) / 2, (p.1 - p.2) / (2 * r)⟩
  left_inv z := by
    ext <;> dsimp
    all_goals field_simp; ring
  right_inv p := by
    ext <;> dsimp
    all_goals field_simp; ring
  map_mul' z w := by
    rcases z with ⟨a, b⟩
    rcases w with ⟨c, e⟩
    ext <;> dsimp
    all_goals rw [← hr]; ring
  map_add' z w := by ext <;> simp <;> ring
  commutes' a := by ext <;> simp

@[simp] theorem splitAlgebra_apply (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    splitAlgebra r hr hr0 z = (z.re + r * z.im, z.re - r * z.im) := rfl

theorem splitAlgebra_star (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    splitAlgebra r hr hr0 (star z) = (splitAlgebra r hr hr0 z).swap := by
  ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star, sub_eq_add_neg]

def plus : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d →+* k := (RingHom.fst k k).comp (splitAlgebra r hr hr0).toRingHom
def minus : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d →+* k := (RingHom.snd k k).comp (splitAlgebra r hr hr0).toRingHom

@[simp] theorem plus_star (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    plus r hr hr0 (star z) = minus r hr hr0 z :=
  congrArg Prod.fst (splitAlgebra_star r hr hr0 z)

@[simp] theorem minus_star (z : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :
    minus r hr hr0 (star z) = plus r hr hr0 z :=
  congrArg Prod.snd (splitAlgebra_star r hr hr0 z)

theorem ext_components {z w : Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d}
    (hp : plus r hr hr0 z = plus r hr hr0 w)
    (hm : minus r hr hr0 z = minus r hr hr0 w) : z = w :=
  (splitAlgebra r hr hr0).injective (Prod.ext hp hm)

variable {n : Type*} [Fintype n] [DecidableEq n]

def plusMatrix : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) →+* Matrix n n k := (plus r hr hr0).mapMatrix
def minusMatrix : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) →+* Matrix n n k := (minus r hr hr0).mapMatrix

theorem matrix_ext_components {A B : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d)}
    (hp : plusMatrix r hr hr0 A = plusMatrix r hr hr0 B)
    (hm : minusMatrix r hr hr0 A = minusMatrix r hr hr0 B) : A = B := by
  apply Matrix.ext
  intro i j
  exact ext_components r hr hr0 (congrFun (congrFun hp i) j) (congrFun (congrFun hm i) j)

def joinMatrix (A B : Matrix n n k) : Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d) :=
  fun i j => (splitAlgebra r hr hr0).symm (A i j, B i j)

@[simp] theorem plusMatrix_join (A B : Matrix n n k) :
    plusMatrix r hr hr0 (joinMatrix r hr hr0 A B) = A := by
  ext i j
  exact congrArg Prod.fst ((splitAlgebra r hr hr0).apply_symm_apply (A i j, B i j))

@[simp] theorem minusMatrix_join (A B : Matrix n n k) :
    minusMatrix r hr hr0 (joinMatrix r hr hr0 A B) = B := by
  ext i j
  exact congrArg Prod.snd ((splitAlgebra r hr hr0).apply_symm_apply (A i j, B i j))

def joinUnits (A B : (Matrix n n k)ˣ) : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ where
  val := joinMatrix r hr hr0 A.val B.val
  inv := joinMatrix r hr hr0 A.inv B.inv
  val_inv := by
    apply matrix_ext_components r hr hr0 <;> simp
  inv_val := by
    apply matrix_ext_components r hr hr0 <;> simp

def splitUnits : (Matrix n n (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic k d))ˣ ≃* (Matrix n n k)ˣ × (Matrix n n k)ˣ where
  toFun g := (Units.map (plusMatrix r hr hr0).toMonoidHom g,
    Units.map (minusMatrix r hr hr0).toMonoidHom g)
  invFun p := joinUnits r hr hr0 p.1 p.2
  left_inv g := by
    apply Units.ext
    apply matrix_ext_components r hr hr0 <;> simp [joinUnits]
  right_inv p := by
    apply Prod.ext <;> apply Units.ext <;> simp [joinUnits]
  map_mul' g h := by simp [map_mul]

end RepresentationTheory.Theta.Adelic.SpecialUnitary.SplitAlgebra

end

end OAI
