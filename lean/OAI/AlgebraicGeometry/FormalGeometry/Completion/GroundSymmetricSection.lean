import OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundAffineComplement
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine

/-! # Ground Symmetric Section -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundSymmetricSection

noncomputable section

/-! An affine neighborhood of the rational identity supplies a symmetric
line bundle and an affine nonvanishing section over the ground field. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

theorem ground_symmetric_affine_section
    {K : Type u} [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyIntegral A.hom] :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf),
      (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s : Set A.left).Nonempty ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ∧
        Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf) := by
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.hom]
    infer_instance⟩
  let j : A.left ≅ A.left := (Over.forget (Spec (CommRingCat.of K))).mapIso (asIso (GrpObj.inv (X := A)))
  have hj : j.hom ≫ j.hom = 𝟙 A.left := congrArg Over.Hom.left (GrpObj.inv_comp_inv A)
  let x : A.left := (MonObj.one (X := A)).left (IsLocalRing.closedPoint K)
  have hjx : j.hom x = x := by
    have h : (MonObj.one (X := A)) ≫ GrpObj.inv = MonObj.one := by simp
    exact congrArg (fun a : Spec (CommRingCat.of K) ⟶ A.left => a (IsLocalRing.closedPoint K))
      (congrArg Over.Hom.left h)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ := A.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨L, s, hs⟩ := GroundAffineComplement.Construction.GroundAffineComplementDivisor.exists_lineBundle A.hom ⟨U, hU⟩
  let M := L.tensor (L.pullback j.hom)
  let t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ M.sheaf := Quotients.FiniteDescent.BinaryTensorId.Construction.BinaryTensorMap.tensorSection s (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j.hom s)
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = U ⊓ j.hom ⁻¹ᵁ U := by
    have h₁ := Quotients.FiniteDescent.TensorSection.Construction.TensorSectionLocus.nonvanishing (L := L) (M := L.pullback j.hom)
      s (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j.hom s)
    have h₂ := Quotients.FiniteDescent.SectionBase.Construction.SectionBaseChange.nonvanishing_pullback j.hom L s
    exact h₁.trans (congrArg₂ (fun V W : A.left.Opens => V ⊓ W) hs
      (h₂.trans (congrArg (fun V => j.hom ⁻¹ᵁ V) hs)))
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback j.hom) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
    let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L
    change Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map j.hom (q * Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map j.hom q) = q * Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map j.hom q
    rw [map_mul]
    have hh : Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map j.hom (Quotients.FiniteDescent.PicardPullbackId.Construction.PicardPullback.map j.hom q) = q := by
      change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.hom q) = q
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hj, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
    rw [hh, mul_comm]
  have hix : x ∈ j.hom ⁻¹ᵁ U := by
    change j.hom x ∈ U
    rwa [hjx]
  refine ⟨M, t, ⟨x, ht.symm ▸ ⟨hx, hix⟩⟩, ?_, Quotient.exact hc⟩
  rw [ht]
  exact hU.inf (hU.preimage j.hom)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroundSymmetricSection
