import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FlatSections
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FractionBaseChangeDomain
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.DomainFunctions
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Affine Field Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineFieldBaseChange.Construction

noncomputable section

/-! # Completion: proper global sections after a field-valued affine base change -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

/-- The actual structural maps give the global-section pushout over the original base ring. -/
theorem proper_fraction_sections_isPushout :
    let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
    IsPushout (CommRingCat.ofHom (algebraMap R K))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd f g).appTop)
      (pullback.fst f g).appTop := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : Flat g := (Flat.SpecMap_iff).mpr (RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat K (nonZeroDivisors R)))
  exact (FlatSections.Construction.proper_flat_affine_sections_isPushout f g).flip.of_iso
    (Scheme.ΓSpecIso (CommRingCat.of R)) (Scheme.ΓSpecIso (CommRingCat.of K))
    (Iso.refl _) (Iso.refl _) (by simp [g]) (by simp) (by simp [g]) (by simp [g])

theorem proper_fraction_globalFunctionDomain_finite [IsDomain Γ(X, ⊤)]
    [Algebra R Γ(X, ⊤)] [FaithfulSMul R Γ(X, ⊤)]
    (hF : CommRingCat.ofHom (algebraMap R Γ(X, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) :
    Module.Finite K (K ⊗[R] Γ(X, ⊤)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let P := pullback f g
  let G : CommRingCat.of K ⟶ Γ(P, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.snd f g).appTop
  let : Algebra K Γ(P, ⊤) := G.hom.toAlgebra
  have H : IsPushout (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (algebraMap R Γ(X, ⊤))) G (pullback.fst f g).appTop := by
    rw [hF]
    exact proper_fraction_sections_isPushout R K f
  let HT := CommRingCat.isPushout_tensorProduct R K Γ(X, ⊤)
  let e : CommRingCat.of (K ⊗[R] Γ(X, ⊤)) ≅ Γ(P, ⊤) :=
    HT.isoIsPushout (CommRingCat.of K) Γ(X, ⊤) H
  have he : CommRingCat.ofHom (algebraMap K (K ⊗[R] Γ(X, ⊤))) ≫ e.hom = G :=
    HT.inl_isoIsPushout_hom _ _ H
  let eA : K ⊗[R] Γ(X, ⊤) ≃ₐ[K] Γ(P, ⊤) := {
    __ := e.commRingCatIsoToRingEquiv
    commutes' k := congrArg (fun φ : CommRingCat.of K ⟶ Γ(P, ⊤) => φ k) he }
  have : IsDomain (K ⊗[R] Γ(X, ⊤)) := FractionBaseChangeDomain.Construction.fraction_tensor_isDomain R K Γ(X, ⊤)
  have : IsDomain Γ(P, ⊤) := eA.symm.toRingEquiv.toMulEquiv.isDomain _
  have hG : G.hom.Finite :=
    (DomainFunctions.Construction.proper_globalFunctionDomain_finite K (pullback.snd f g)).comp
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective)
  have : Module.Finite K Γ(P, ⊤) := hG
  exact Module.Finite.of_injective eA.toLinearMap eA.injective

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineFieldBaseChange.Construction
