import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.SheafOverlapEquivalence

/-! # Section Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionDifference

noncomputable section

/-! The difference of pairwise restrictions has the actual global section module as its kernel. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite

universe u v

variable {R : Type u} [CommRing R] {X : TopCat.{u}}
    (F : TopCat.Presheaf (ModuleCat.{u} R) X) {ι : Type v} (U : ι → Opens X)

def openSectionDifference : ((i : ι) → F.obj (op (U i))) →ₗ[R]
    ((i j : ι) → F.obj (op (U i ⊓ U j))) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    ((F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op).hom.comp (LinearMap.proj i)) -
      ((F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op).hom.comp (LinearMap.proj j))

theorem openSectionDifference_ker :
    (openSectionDifference F U).ker = Module.SheafOverlapEquivalence.compatibleOpenSectionModule F U := by
  apply Submodule.ext
  intro x
  change (fun i j ↦ F.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (x i) -
    F.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (x j)) = 0 ↔ _
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero]
  rfl

def globalOpenSectionKernelEquiv (hF : F.IsSheaf) (hU : iSup U = ⊤) :
    F.obj (op ⊤) ≃ₗ[R] (openSectionDifference F U).ker :=
  (Module.SheafOverlapEquivalence.globalOpenSectionEquiv F U hF hU).trans
    (LinearEquiv.ofEq _ _ (openSectionDifference_ker F U).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.SectionDifference
