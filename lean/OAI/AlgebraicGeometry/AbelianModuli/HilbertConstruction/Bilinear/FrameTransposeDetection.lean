import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameSectionTranspose
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.SectionContraction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.OpenMapGluing

/-! # Frame Transpose Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameTransposeDetection

noncomputable section

/-! Vanishing of the transposed global section forces the original contracted pairing to vanish as a module morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {D : OpenFrame.Transitions.OpenFrameTransitions U}
variable {M Q : X.Modules} (F : CompatibleSheaf.CompatibleSheafFrames D.reciprocal Q)
variable (β : Sheaves.SheafBilinearMap M Q (Line.Bundles.structureModule X))

theorem contractLeft_eq_zero_of_pairingFrameSectionMap_eq_zero
    (hU : ∀ x : X, ∃ i, x ∈ U i) (s : Γ(M, ⊤)) (hs : FrameSectionTranspose.pairingFrameSectionMap F β s = 0) :
    β.contractLeft s = 0 := by
  have ht : FrameCoefficientTuples.pairingFrameTupleMap F β s = 0 := by
    have h := FrameSectionTranspose.pairingFrameSectionMap_tuple F β s
    rw [hs, map_zero] at h
    exact h.symm
  apply Module.BasisIsomorphisms.moduleMap_eq_of_basis (Module.OpenMapGluing.subordinateOpenBasis U) (Module.OpenMapGluing.subordinateOpenBasis_isBasis U hU)
  intro V
  obtain ⟨i, hi⟩ := V.property
  apply ConcreteCategory.hom_ext
  intro q
  have hz : FrameCoefficientTuples.pairingFrameCoefficient F β s i = 0 := congrFun ht i
  have hv : β.app V.val (M.presheaf.map V.val.leTop.op s) (F.frame V.val i hi 1) = 0 := by
    have h := FrameCoefficientTuples.pairingFrameCoefficient_restrict F β s V.val i hi
    rw [hz, map_zero] at h
    exact h.symm
  have hq : q = (F.frame V.val i hi).symm q • F.frame V.val i hi 1 := by
    have h := (F.frame V.val i hi).map_smul ((F.frame V.val i hi).symm q) (1 : Γ(X, V.val))
    simp only [smul_eq_mul, mul_one] at h
    exact ((F.frame V.val i hi).apply_symm_apply q).symm.trans h
  change β.app V.val (M.presheaf.map V.val.leTop.op s) q = 0
  rw [hq, LinearMap.map_smul, hv, smul_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bilinear.FrameTransposeDetection
