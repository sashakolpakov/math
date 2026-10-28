import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorSectionComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CoverTensorComparison

/-! # Global Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalTensorComparison

noncomputable section

/-! Flat affine base change commutes with global functions on a quasi-compact scheme
with affine diagonal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S X Y P : Scheme.{u}} [IsAffine S] [IsAffine Y] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem flat_globalTensorComparison_isIso
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    IsIso ((Affine.TensorSectionComparison.baseChangeTensorSectionComparison H).app (.op ⊤)) := by
  let C := X.affineCover.finiteSubcover
  let U : C.I₀ → X.Opens := fun i => (C.f i).opensRange
  have hU (i : C.I₀) : IsAffineOpen (U i) := by
    have : IsAffine (C.X i) := by
      change IsAffine (X.affineCover.X _)
      infer_instance
    exact isAffineOpen_opensRange (C.f i)
  have hpair (i : Pairwise C.I₀) :
      IsIso ((Affine.TensorSectionComparison.baseChangeTensorSectionComparison H).app (.op ((Pairwise.diagram U).obj i))) := by
    apply Affine.TensorSectionComparison.affineOpen_tensorComparison_isIso H
    cases i with
    | single i => exact hU i
    | pair i j => exact (hU i).inf (hU j)
  have : Module.Flat Γ(S, ⊤) ((AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj
      (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) :=
    (inferInstance : Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g))
  have h := Finite.CoverTensorComparison.finiteCoverTensorComparison_isIso (AlgebraSectionModules.algebraSectionModulePresheaf f.appTop.hom)
    (Tensor.SectionModules.inverseImageSectionModules a f.appTop.hom) (AlgebraSectionModules.algebraSectionModulePresheaf_isSheaf _)
    (Tensor.SectionModules.inverseImageSectionModules_isSheaf _ _) ((AlgebraSectionModules.commAlgToModules Γ(S, ⊤)).obj
      (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) (Affine.TensorSectionComparison.baseChangeTensorSectionComparison H) U hpair
  have htop : iSup U = ⊤ := C.iSup_opensRange
  exact (congrArg (fun V : X.Opens =>
    IsIso ((Affine.TensorSectionComparison.baseChangeTensorSectionComparison H).app (.op V))) htop).mp h

theorem flat_globalTensorComparison_bijective
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    Function.Bijective ((Affine.TensorSectionComparison.baseChangeTensorSectionComparison H).app (.op ⊤)) := by
  have := flat_globalTensorComparison_isIso H
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.GlobalTensorComparison
