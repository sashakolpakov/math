import OAI.NumberTheory.PadicHodge.GeometricComparison.TensorCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.PowerFiltration

/-! # Coefficient Coordinates Filtration -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientCoordinatesFiltration.CoefficientCoordinates

noncomputable section

/-! Coefficient coordinates identify the actual extended filtration with its pointwise product. -/

open scoped TensorProduct

variable {K L I V : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype I] [DecidableEq I] [AddCommGroup V] [Module K V]

theorem subspace (b : Module.Basis I K L) (P : Submodule K V) :
    ((P.baseChange L).restrictScalars K).map (TensorCoordinates.CoefficientCoordinates.equiv b).toLinearMap =
      Submodule.pi Set.univ (fun _ : I => P) := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hx
    change TensorCoordinates.CoefficientCoordinates.equiv b (P.subtype.baseChange L z) ∈ Submodule.pi Set.univ (fun _ : I => P)
    rw [TensorCoordinates.CoefficientCoordinates.naturality]
    exact Submodule.mem_pi.mpr (fun i _ => (TensorCoordinates.CoefficientCoordinates.equiv b z i).property)
  · intro hy
    let yP : I → P := fun i => ⟨y i, Submodule.mem_pi.mp hy i (Set.mem_univ i)⟩
    let z := (TensorCoordinates.CoefficientCoordinates.equiv b).symm yP
    refine ⟨P.subtype.baseChange L z, ⟨z, rfl⟩, ?_⟩
    change TensorCoordinates.CoefficientCoordinates.equiv b (P.subtype.baseChange L z) = y
    rw [TensorCoordinates.CoefficientCoordinates.naturality]
    ext i
    exact congrArg Subtype.val (congrFun ((TensorCoordinates.CoefficientCoordinates.equiv b).apply_symm_apply yP) i)

theorem filtration (b : Module.Basis I K L) (F : Linear.FiniteFiltration K V) (i : ℤ) :
    (((Linear.restrictScalarFiltration L (Linear.finiteCoefficientFiltration L F)).step i).map
      (TensorCoordinates.CoefficientCoordinates.equiv b).toLinearMap) = (PowerFiltration.FiltrationTransport.power I F).step i :=
  subspace b (F.step i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientCoordinatesFiltration.CoefficientCoordinates
