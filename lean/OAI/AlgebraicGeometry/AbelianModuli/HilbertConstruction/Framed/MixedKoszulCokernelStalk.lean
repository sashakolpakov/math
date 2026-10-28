import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.KoszulGermSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleStalk
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ScalarKoszul.CoefficientCokernel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedKoszulCokernelEuler

/-! # Mixed Koszul Cokernel Stalk -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulCokernelStalk

noncomputable section

/-! At a common zero, the stalk of the framed mixed Koszul cokernel
is a quotient by a proper ideal in the actual local ring. Hence it is
nonzero, without a reducedness or transversality assumption. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem framedMixedKoszulCokernel_stalk_nonzero
    {X : Scheme.{u}} (x : X) (M : X.Modules) (eM : M ≅ Line.Bundles.structureModule X)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X))
    (frames : ∀ b ∈ bs, Nonempty (b.1.sheaf ≅ Line.Bundles.structureModule X))
    (hx : x ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs) :
    ¬ IsZero ((Module.StalkExactness.moduleStalkFunctor x).obj (MixedKoszulCokernelEuler.mixedKoszulCokernel M bs)) := by
  classical
  let R := X.presheaf.stalk x
  let F := Module.StalkExactness.moduleStalkFunctor x
  let φ : Γ(X, ⊤) →+* R := (X.presheaf.germ ⊤ x trivial).hom
  let ρ : LineBundleKoszulComplex.LineBundleSection X → R := fun b =>
    if hb : b ∈ bs then φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ (Classical.choice (frames b hb)).hom)) else 0
  have hρ : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b := by
    intro b hb
    exact ⟨Classical.choice (frames b hb), by simp only [ρ, dite_eq_left hb]⟩
  let rs := bs.map ρ
  have hle : Regular.SequenceBasic.Ideal.ofList rs ≤ maximalIdeal R := by
    have hpoint : IsLocalRing.closedPoint R ∈
        PrimeSpectrum.zeroLocus (Regular.SequenceBasic.Ideal.ofList rs : Set R) := by
      rw [KoszulGermSupport.framedKoszul_germ_zeroLocus x bs ρ hρ]
      change X.fromSpecStalk x (IsLocalRing.closedPoint R) ∈ MixedKoszulGeometricSupport.mixedSectionZeroSet bs
      rw [Scheme.fromSpecStalk_closedPoint]
      exact hx
    exact hpoint
  have hproper : Regular.SequenceBasic.Ideal.ofList rs ≠ ⊤ := fun he =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_unique (he ▸ hle))
  let C := LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs
  let eC := MixedKoszulFunctor.framedMixedKoszulFunctorIso F φ (Structure.ModuleStalk.moduleStalkFunctor_globalScalar x) M bs ρ hρ
  let eQ := PreservesCokernel.iso F (C.d (-1) 0) ≪≫ ScalarKoszul.CoefficientCokernel.cochainFinalCokernelIso eC
  let eV := F.mapIso eM ≪≫ Structure.ModuleStalk.structureModuleStalkIso x
  intro hz
  exact ScalarKoszul.CoefficientCokernel.scalarKoszulRankOneCokernel_nonzero (F.obj M) eV rs hproper (eQ.isZero_iff.mp hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulCokernelStalk
