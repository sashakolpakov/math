import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixSubmoduleAlgebraEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.Archimedean.LieMem

/-! # Mixed Basis -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedBasis.Construction

noncomputable section

/-! A basis of the rational Lie algebra extends to a free basis of its
Minkowski coefficient module. -/

open scoped Classical TensorProduct _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField _root_.NumberField.mixedEmbedding

attribute [local instance] LieRing.ofAssociativeRing Minkowski.LieEq.Construction.mixedSpaceBaseAlgebra

theorem matrixSubmoduleAlgebraExtension_eq_lieMixedModule
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    MatrixFlatExtension.Construction.matrixSubmoduleAlgebraExtension (R := mixedSpace k) (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule =
      MixedLattice.Construction.lieMixedModule G := by
  rw [MatrixFlatExtension.Construction.matrixSubmoduleAlgebraExtension_eq_span, MixedLattice.Construction.lieMixedModule_eq_matrix_span]
  rfl

def lieMixedScalarEquiv
    {k : Type} [Field k] [NumberField k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) :
    mixedSpace k ⊗[k] Infinitesimal.Action.Construction.infinitesimalStabilizer G ≃ₗ[mixedSpace k] MixedLattice.Construction.lieMixedModule G :=
  (MatrixSubmoduleAlgebraEquiv.Construction.matrixSubmoduleAlgebraEquiv (Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule).trans
    (LinearEquiv.ofEq _ _ (matrixSubmoduleAlgebraExtension_eq_lieMixedModule G))

theorem lieMixedScalarEquiv_tmul_coe
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (a : mixedSpace k) (A : Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    (lieMixedScalarEquiv G (a ⊗ₜ[k] A)).val = a • A.val.map (mixedEmbedding k) :=
  MatrixSubmoduleAlgebraEquiv.Construction.matrixSubmoduleAlgebraMap_tmul _ a A

def lieMixedBasis
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Module.Basis ι k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) :
    Module.Basis ι (mixedSpace k) (MixedLattice.Construction.lieMixedModule G) :=
  (b.baseChange (mixedSpace k)).map (lieMixedScalarEquiv G)

theorem lieMixedBasis_coe
    {k ι : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Module.Basis ι k (Infinitesimal.Action.Construction.infinitesimalStabilizer G)) (i : ι) :
    (lieMixedBasis G b i).val = (b i).val.map (mixedEmbedding k) := by
  rw [lieMixedBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    lieMixedScalarEquiv_tmul_coe, one_smul]

def archimedeanLieAlgebraEquiv
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) : MixedLattice.Construction.lieMixedModule G ≃ₗ[mixedSpace k] MixedLattice.Construction.lieMixedModule G :=
  { (Archimedean.LieMem.Construction.archimedeanLieEquiv G hG g).toAddEquiv with
    map_smul' := fun a A => Subtype.ext
      ((Archimedean.LieMem.Construction.matrixUnitConjugationEquiv (Archimedean.LieMem.Construction.archimedeanLieUnit G g)).map_smul a A.val) }

theorem archimedeanLieAlgebraEquiv_restrictScalars
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (g : Archimedean.ExteriorAction.Construction.fullArchimedeanMatrixGroup G) :
    (archimedeanLieAlgebraEquiv G hG g).restrictScalars ℝ = Archimedean.LieMem.Construction.archimedeanLieEquiv G hG g := by
  apply LinearEquiv.ext
  intro A
  rfl

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Lie.MixedBasis.Construction
