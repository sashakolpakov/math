import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineComplement
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionBase
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PicardPullbackId
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupIrreducibleOf
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SchemeSmooth

/-! # Symmetric Affine -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine.Construction.SymmetricAffineSections

noncomputable section

/-! Symmetric line bundles with affine section neighborhoods, constructed
without assuming that the scheme already has an ample bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

theorem exists_of_involution {K : Type u} [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of K)) [Smooth f] (j : X ≅ X) (hj : j.hom ≫ j.hom = 𝟙 X)
    (hAF : ∀ F : Set X, F.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ U) (x : X) :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf),
      x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ∧
      Nonempty ((L.pullback j.hom).sheaf ≅ L.sheaf) := by
  obtain ⟨U, hU, hFU⟩ := hAF {x, j.hom x} (Set.toFinite _)
  have hx : x ∈ U := hFU (by simp)
  have hjx : j.hom x ∈ U := hFU (by simp)
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨L, s, hs⟩ := AffineComplement.Construction.AffineComplementDivisor.exists_lineBundle f ⟨U, hU⟩
  let M := L.tensor (L.pullback j.hom)
  let t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M.sheaf := BinaryTensorId.Construction.BinaryTensorMap.tensorSection s (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j.hom s)
  have ht : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t = U ⊓ j.hom ⁻¹ᵁ U := by
    have h₁ := TensorSection.Construction.TensorSectionLocus.nonvanishing (L := L) (M := L.pullback j.hom)
      s (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j.hom s)
    have h₂ := SectionBase.Construction.SectionBaseChange.nonvanishing_pullback j.hom L s
    exact h₁.trans (congrArg₂ (fun V W : X.Opens => V ⊓ W) hs
      (h₂.trans (congrArg (fun V => j.hom ⁻¹ᵁ V) hs)))
  have hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (M.pullback j.hom) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M := by
    let q := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L
    change PicardPullbackId.Construction.PicardPullback.map j.hom (q * PicardPullbackId.Construction.PicardPullback.map j.hom q) =
      q * PicardPullbackId.Construction.PicardPullback.map j.hom q
    rw [map_mul]
    have hh : PicardPullbackId.Construction.PicardPullback.map j.hom (PicardPullbackId.Construction.PicardPullback.map j.hom q) = q := by
      change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j.hom q) = q
      rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hj, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
    rw [hh, mul_comm]
  refine ⟨M, t, ht.symm ▸ ⟨hx, hjx⟩, ?_, Quotient.exact hc⟩
  rw [ht]
  exact hU.inf (hU.preimage j.hom)

/-- Every point of a proper smooth connected commutative group over an
algebraically closed field has an affine section neighborhood for a line
bundle invariant under inversion. -/
theorem exists_for_group {K : Type u} [Field K] [IsAlgClosed K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom] (x : A.left) :
    ∃ (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ⟶ L.sheaf),
      x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ∧ IsAffineOpen (AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing s) ∧
      Nonempty ((L.pullback (GrpObj.inv (X := A)).left).sheaf ≅ L.sheaf) := by
  have : IsReduced A.left := SchemeSmooth.Construction.SchemeSmoothReduced.reduced_of_smooth_field A.hom
  have : IrreducibleSpace A.left := GroupIrreducibleOf.Construction.GroupIrreducible.irreducibleSpace_of_connected_group A
  have : IsIntegral A.left := isIntegral_of_irreducibleSpace_of_isReduced A.left
  have : A.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from A.hom]
    infer_instance⟩
  let j := (Over.forget (Spec (.of K))).mapIso (asIso (GrpObj.inv (X := A)))
  have hj : j.hom ≫ j.hom = 𝟙 A.left := congrArg Over.Hom.left (GrpObj.inv_comp_inv A)
  exact exists_of_involution A.hom j hj (GroupIrreducibleOf.Construction.GroupIrreducible.exists_affineOpen_of_finite A) x

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.SymmetricAffine.Construction.SymmetricAffineSections
