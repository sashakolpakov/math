import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace
import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum
import OAI.RepresentationTheory.Weil.Local.Generators

/-! # Normalization -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction

noncomputable section

section

/-!
Explicit scalar normalizations, rather than an uninterpreted predicate.

For the open cell det(g-1) ≠ 0, use the model-independent Schrödinger
intertwiner obtained by the regularized Heisenberg integral. The scalar is
the unitary normalization of Murase, Proc. Japan Acad. 77A (2001), §1.4–1.8,
applied to each factor of the tensor pair. For Tr(hV*hW)/2 the quadratic
Weil constant is γ_ψ(1) γ_ψ(-d). Scaling K by δ⁻¹ makes it Hermitian; scaling
H by δ makes it skew-Hermitian. Both splitting characters occur explicitly.
The conditions only concern local operators; no adelic or rational
compatibility is assumed.

Source: https://doi.org/10.3792/pjaa.77.59
-/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology BigOperators

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

section Local
variable (k : Type) [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (N : ℕ) (ψ : AddChar k ℂ)

def phasePair (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N) : k :=
  -(Matrix.J (Fin N) k).toBilin' x y

def openCellScale (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) : ℝ :=
  if h : (g.val - 1).det ≠ 0 then
    Real.sqrt (Weil.Local.FunctionsMetaplectic.Construction.localModulus k (Units.mk0 (g.val - 1).det h)) else 0

/-- Damping regularizes the oscillatory integral at archimedean and finite
places alike; the intended normalization uses its limit as ε tends to zero
through positive real numbers. -/
def dampedIntertwiner (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (ε : ℝ)
    (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  (openCellScale k N g : ℂ) *
    ∫ w : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace k N,
      Complex.exp (-((ε * ∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ)) *
        ψ (phasePair k N w (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g w) / 2) *
        Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (fun i => w i - Weil.Local.FunctionsMetaplectic.Construction.symplecticAction g w i) f x
      ∂(Measure.pi (fun _ => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ))

def openCellOperator (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => dampedIntertwiner k N ψ g ε f x)

def quadraticWeilConstant (d : k) : ℂ := Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 * Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex k ψ (-d)

end Local

def deltaUnit {k : Type*} [Field k] (d : k) (hd : d ≠ 0) : (UnitaryBase.Construction.Quadratic k d)ˣ where
  val := ⟨0, 1⟩
  inv := ⟨0, d⁻¹⟩
  val_inv := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, hd]
  inv_val := by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, hd]

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)
  (n m : ℕ) (C : Characters.Construction.GlobalCharacters F d n m)

def localDelta (v : ArchimedeanAdeles.Construction.Places F) : (ArchimedeanAdeles.Construction.localQuadratic F d v)ˣ :=
  deltaUnit (ArchimedeanAdeles.Construction.rationalScalar F v d)
    (fun h => hd ((ArchimedeanAdeles.Construction.rationalScalar F v).injective (h.trans (map_zero (ArchimedeanAdeles.Construction.rationalScalar F v)).symm)))

def normCharacterScalar (v : ArchimedeanAdeles.Construction.Places F) (a : ArchimedeanAdeles.Construction.Completion F v) : Circle :=
  if h : a ≠ 0 then Characters.Construction.normCharacter F d v (Units.mk0 a h) else 1

def firstFactorScalar (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : ℂ :=
  (quadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
    ((normCharacterScalar F d v
      ((localDelta F d hd v)⁻¹ ^ m * Matrix.GeneralLinearGroup.det K).val.re : Circle) : ℂ) ^ n *
    (Characters.Construction.localCharacter F d C.χW v
      ((localDelta F d hd v) ^ n * Matrix.GeneralLinearGroup.det H * Matrix.GeneralLinearGroup.det u) : ℂ)

def secondFactorScalar (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ) : ℂ :=
  (quadraticWeilConstant (ArchimedeanAdeles.Construction.Completion F v) (Characters.Construction.localAdditiveCharacter F C.ψ v)
      (ArchimedeanAdeles.Construction.rationalScalar F v d))⁻¹ ^ (n * m) *
    ((normCharacterScalar F d v (Matrix.GeneralLinearGroup.det H).val.re : Circle) : ℂ) ^ m *
    (Characters.Construction.localCharacter F d C.χV v
      (Matrix.GeneralLinearGroup.det K * Matrix.GeneralLinearGroup.det u) : ℂ)

/-- Explicit local normalization on the two open unitary cells. A continuous
homomorphism is constrained on each factor, not merely required to cover it. -/
def LocalNormalization (v : ArchimedeanAdeles.Construction.Places F)
    (H : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (K : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ)
    (c : TensorSpace.Construction.SymplecticFrame (ArchimedeanAdeles.Construction.rationalScalar F v d) n m H.val K.val)
    (s : UnitaryBase.Construction.Unitary H.val × UnitaryBase.Construction.Unitary K.val →ₜ* Vacuum.Construction.CoverAt F (n * m) C.ψ v) : Prop :=
  (∀ (g : UnitaryBase.Construction.Unitary H.val) (u : (Matrix (Fin n) (Fin n) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ),
    u.val = g.val.val - 1 →
      ∀ (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m)),
        (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) (s (g, 1)) f).val x =
          firstFactorScalar F d hd n m C v H K u *
            openCellOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
              (TensorSpace.Construction.dualPairSymplectic H.val K.val c (g, 1)) f.val x) ∧
  (∀ (g : UnitaryBase.Construction.Unitary K.val) (u : (Matrix (Fin m) (Fin m) (ArchimedeanAdeles.Construction.localQuadratic F d v))ˣ),
    u.val = g.val.val - 1 →
      ∀ (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F v) (n * m)) (x : Weil.Local.FunctionsMetaplectic.Construction.Position (ArchimedeanAdeles.Construction.Completion F v) (n * m)),
        (Oscillator.Construction.localOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v) (s (1, g)) f).val x =
          secondFactorScalar F d n m C v H K u *
            openCellOperator (ArchimedeanAdeles.Construction.Completion F v) (n * m) (Characters.Construction.localAdditiveCharacter F C.ψ v)
              (TensorSpace.Construction.dualPairSymplectic H.val K.val c (1, g)) f.val x)

end

/-! A trivial local character makes the specified regularized open-cell
operator vanish in positive dimension. This will exclude such characters
using the invertibility of the supplied normalized local splittings. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology Classical

open OAI.RepresentationTheory.Weil.Local.Generators.Construction

variable (k : Type) [NormedField k] [Infinite k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k ℂ)
  (hψ : ∀ x, ψ x = 1)

include hψ in
theorem selfDualMeasure_trivial : Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ = 0 := by
  have hf (ξ : k) : Weil.Local.FunctionsMetaplectic.Construction.referenceFourier k ψ ξ =
      ((Measure.addHaar : Measure k).real (Weil.Local.FunctionsMetaplectic.Construction.referenceCompact k : Set k) : ℂ) := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.referenceFourier, hψ, integral_const, measureReal_def]
  have hs : Weil.Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ = 0 := by
    simp [Weil.Local.FunctionsMetaplectic.Construction.fourierHaarScaleSquared, hf, integral_const, measureReal_def]
  simp [Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure, hs]

omit [Infinite k] in
theorem openCellOperator_of_measure_zero (hμ : Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ = 0)
    (N : ℕ) (hN : 0 < N)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    openCellOperator k N ψ g f x = 0 := by
  have hzero : Measure.pi (fun _ : Fin N ⊕ Fin N => Weil.Local.FunctionsMetaplectic.Construction.selfDualMeasure k ψ) = 0 := by
    simp only [hμ]
    apply (Measure.measure_univ_eq_zero).mp
    rw [Measure.pi_univ]
    exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl ⟨0, hN⟩)) rfl
  have hd (ε : ℝ) : dampedIntertwiner k N ψ g ε f x = 0 := by
    simp [dampedIntertwiner, hzero]
  simp only [openCellOperator, hd]
  exact tendsto_const_nhds.limUnder_eq

include hψ in
theorem openCellOperator_trivial (N : ℕ) (hN : 0 < N)
    (g : Weil.Local.FunctionsMetaplectic.Construction.Symplectic k N) (f : Weil.Local.FunctionsMetaplectic.Construction.Position k N → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position k N) :
    openCellOperator k N ψ g f x = 0 :=
  openCellOperator_of_measure_zero k ψ (selfDualMeasure_trivial k ψ hψ) N hN g f x

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Normalization.Construction
