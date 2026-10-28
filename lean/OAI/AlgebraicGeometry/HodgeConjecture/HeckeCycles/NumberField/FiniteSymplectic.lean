import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum
import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Finite Symplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic.CM

noncomputable section

/-! Assemble the actual restricted family of local symplectic matrices
into one symplectic matrix over the number field's finite adele ring. -/

open scoped Classical _root_.NumberField _root_.Matrix
open Filter _root_.Matrix OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction

variable (F : Type) [Field F] [NumberField F] (N : ℕ)

abbrev Place := IsDedekindDomain.HeightOneSpectrum (𝓞 F)
abbrev Group := RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup (fun v : Place F => RepresentationTheory.Weil.AdelicSplitting.Vacuum.Construction.symplecticIntegral F N (.inr v))

def evaluation (v : Place F) : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F →+* v.adicCompletion F :=
  RestrictedProduct.evalRingHom (fun w : Place F => w.adicCompletion F) v

def matrix (g : Group F N) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) :=
  fun i j => ⟨fun v => (g v).val i j, by
    filter_upwards [g.property] with v hv
    exact hv.1 i j⟩

theorem matrix_evaluation (g : Group F N) (v : Place F) :
    (matrix F N g).map (evaluation F v) = (g v).val := rfl

theorem matrix_ext {I : Type*} (A B : Matrix I I (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F))
    (h : ∀ v : Place F, A.map (evaluation F v) = B.map (evaluation F v)) : A = B := by
  apply Matrix.ext
  intro i j
  apply RestrictedProduct.ext
  intro v
  exact congrFun (congrFun (h v) i) j

theorem matrix_symplectic (g : Group F N) :
    matrix F N g ∈ Matrix.symplecticGroup (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) := by
  apply SymplecticGroup.mem_iff'.mpr
  apply matrix_ext F
  intro v
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_J,
    matrix_evaluation, SymplecticGroup.mem_iff'.mp (g v).property]

def assemble : Group F N →* RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) where
  toFun g := ⟨matrix F N g, matrix_symplectic F N g⟩
  map_one' := by
    apply Subtype.ext
    apply matrix_ext F
    intro v
    rw [matrix_evaluation]
    change (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (v.adicCompletion F)) =
      (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F)).map (evaluation F v)
    exact ((evaluation F v).mapMatrix.map_one).symm
  map_mul' g h := by
    apply Subtype.ext
    apply matrix_ext F
    intro v
    change (matrix F N (g * h)).map (evaluation F v) =
      (matrix F N g * matrix F N h).map (evaluation F v)
    rw [matrix_evaluation, Matrix.map_mul, matrix_evaluation, matrix_evaluation]
    rfl

theorem assemble_evaluation (g : Group F N) (v : Place F) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (evaluation F v) (assemble F N g) = g v :=
  Subtype.ext (matrix_evaluation F N g v)

theorem assemble_injective : Function.Injective (assemble F N) := by
  intro g h he
  apply RestrictedProduct.ext
  intro v
  exact (assemble_evaluation F N g v).symm.trans
    ((congrArg (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (evaluation F v)) he).trans (assemble_evaluation F N h v))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.NumberField.FiniteSymplectic.CM
