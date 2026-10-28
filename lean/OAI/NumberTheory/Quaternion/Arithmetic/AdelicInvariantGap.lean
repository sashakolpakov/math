import OAI.NumberTheory.Quaternion.Arithmetic.MinkowskiLocalProjections
import OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap

/-! # Adelic Invariant Gap -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdelicInvariantGap

noncomputable section

/-! A polynomial invariant with no nonzero rational zero gives a
uniform Minkowski vector gap over all its finite-adelic lattices. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField _root_.NumberField.mixedEmbedding OAI.NumberTheory.ArithmeticGroups.Lattices.InvariantGap.Construction Set
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

theorem uniform_minkowski_gap_of_adelic_invariant (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (p : MvPolynomial (Fin n) F) (hp0 : MvPolynomial.eval (0 : Fin n → F) p = 0)
    (hfinite : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : LocalAdeles.LocalPoints G (.inr v)) (y : Fin n → v.adicCompletion F),
      MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) (h.val.val *ᵥ y) p =
        MvPolynomial.eval₂Hom (LocalAdeles.localEmbedding (.inr v)) y p)
    (harch : ∀ (v : InfinitePlace F) (h : G.AtPlace v) (y : Fin n → v.Completion),
      MvPolynomial.eval₂Hom (algebraMap F v.Completion) (h.val.val *ᵥ y) p =
        MvPolynomial.eval₂Hom (algebraMap F v.Completion) y p)
    (hne : ∀ x : Fin n → F, x ≠ 0 → MvPolynomial.eval x p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G) (h : G.ArchimedeanProduct Set.univ),
      ∀ x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g), x ≠ 0 →
        ε ≤ ‖ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
          (fun i => mixedEmbedding F (x i))‖ := by
  obtain ⟨d, hd, hvalues⟩ := AdelicPolynomialInvariants.finiteAdelicGroupLattice_invariant_values G p hfinite
  have hdF : (d : F) ≠ 0 := by exact_mod_cast hd
  let P : (Fin n → mixedSpace F) → mixedSpace F :=
    fun y => mixedEmbedding F (d : F) * MinkowskiLocalProjections.mixedPolynomialValue p y
  have hP : Continuous P := continuous_const.mul (MinkowskiLocalProjections.continuous_mixedPolynomialValue p)
  have hpzero : MinkowskiLocalProjections.mixedPolynomialValue p (0 : Fin n → mixedSpace F) = 0 := by
    have he := MinkowskiLocalProjections.mixedPolynomialValue_diagonal p (0 : Fin n → F)
    have hz : (fun i : Fin n => mixedEmbedding F ((0 : Fin n → F) i)) =
        (0 : Fin n → mixedSpace F) := by
      funext i
      exact map_zero (mixedEmbedding F)
    rw [hz, hp0, map_zero] at he
    exact he
  have hP0 : P 0 = 0 := by simp only [P, hpzero, mul_zero]
  let D : Set (mixedSpace F) := mixedEmbedding.integerLattice F
  let S : Set (Fin n → mixedSpace F) := {y | ∃ (g : FiniteAdelicMatrices.FiniteAdelicGroupPoints G)
    (h : G.ArchimedeanProduct Set.univ) (x : Fin n → F),
    x ∈ FiniteAdelicLattice.finiteAdelicMatrixLattice (FiniteAdelicMatrices.finiteAdelicMatrix G g) ∧ x ≠ 0 ∧
      y = ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
        (fun i => mixedEmbedding F (x i))}
  have hS : ∀ y ∈ S, P y ∈ D ∧ P y ≠ 0 := by
    rintro y ⟨g, h, x, hx, hx0, rfl⟩
    have he : P (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.archimedeanRealRepresentation F n (ArithmeticGroups.Lattices.Archimedean.Quotient.Construction.fullArchimedeanPointsEquiv G h).val
        (fun i => mixedEmbedding F (x i))) = mixedEmbedding F ((d : F) * MvPolynomial.eval x p) := by
      dsimp only [P]
      rw [MinkowskiLocalProjections.mixedPolynomialValue_archimedean_invariant G p harch, MinkowskiLocalProjections.mixedPolynomialValue_diagonal, ← map_mul]
    rw [he]
    constructor
    · obtain ⟨u, hu⟩ := hvalues g x hx
      refine ⟨u, ?_⟩
      exact congrArg (mixedEmbedding F) hu
    · intro hz
      exact (mul_ne_zero hdF (hne x hx0))
        ((mixedEmbedding_injective F) (hz.trans (map_zero (mixedEmbedding F)).symm))
  obtain ⟨ε, hε, hgap⟩ := ArithmeticGroups.Lattices.InvariantGap.Construction.uniform_gap_of_discrete_values P hP hP0 D
    ((SetLike.isDiscrete_iff_discreteTopology (s := mixedEmbedding.integerLattice F)).mpr inferInstance)
    (mixedEmbedding.integerLattice F).zero_mem S hS
  exact ⟨ε, hε, fun g h x hx hx0 => hgap _ ⟨g, h, x, hx, hx0, rfl⟩⟩

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdelicInvariantGap
