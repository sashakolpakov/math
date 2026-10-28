import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CoefficientSheaf
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Topology.ContinuousMap.LocallyConstant

/-! # Constant Scheme -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ConstantScheme.Construction

noncomputable section

/-!
# Completion: finite coefficients are represented by finite étale constant schemes

We reuse the checked disjoint-union construction and its base-change
isomorphism from HilbertConstruction. The Completion checker rebuilds and audits those dependencies.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (S : Scheme.{u}) (I : Type u)

theorem finiteConstantScheme_etale : Etale (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @Etale.{u}) (Q := @RingHom.Etale)
  change Etale (Sigma.desc (fun _ : I => 𝟙 S))
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{u})
    (fun _ => inferInstanceAs (Etale (𝟙 S)))

theorem finiteConstantScheme_isClosedMap [Finite I] :
    IsClosedMap (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
  intro C hC
  have heq : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom '' C =
      ⋃ i : I, (Sigma.ι (fun _ : I => S) i) ⁻¹' C := by
    ext s
    constructor
    · rintro ⟨x, hx, hs⟩
      obtain ⟨⟨i, t⟩, rfl⟩ := (sigmaMk (fun _ : I => S)).surjective x
      rw [sigmaMk_mk] at hs hx
      have ht : t = s := (congrArg (fun f : S ⟶ S => f t)
        (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom (S := S) i)).symm.trans hs
      subst t
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    · intro hs
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
      exact ⟨Sigma.ι (fun _ : I => S) i s, hi,
        congrArg (fun f : S ⟶ S => f s) (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme_ι_hom i)⟩
  rw [heq]
  exact isClosed_iUnion_of_finite (fun i => hC.preimage (Sigma.ι (fun _ : I => S) i).continuous)

theorem finiteConstantScheme_affine [Finite I] : IsAffineHom (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
  constructor
  intro U hU
  have : IsAffine U.toScheme := hU
  have : IsAffine (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme U.toScheme I).left :=
    inferInstanceAs (IsAffine (∐ fun _ : I => U.toScheme))
  let e : (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme U.toScheme I).left ≅
      ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom ⁻¹ᵁ U).toScheme :=
    ((Over.forget U.toScheme).mapIso (AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso U.ι I)) ≪≫
      pullbackRestrictIsoRestrict (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom U
  exact IsAffine.of_isIso e.inv

theorem finiteConstantScheme_universallyClosed [Finite I] :
    UniversallyClosed (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom where
  universally_isClosedMap {X Y} i₁ i₂ f h := by
    let e := AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSchemeBaseChangeIso i₂ I
    have hsnd : IsClosedMap (pullback.snd (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom i₂) := by
      have he : e.inv.left ≫ (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme Y I).hom =
          pullback.snd (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom i₂ := e.inv.w
      exact he ▸ (finiteConstantScheme_isClosedMap Y I).comp
        (((Over.forget Y).mapIso e).inv.homeomorph.isClosedMap)
    have he : h.flip.isoPullback.hom ≫ pullback.snd (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom i₂ = f :=
      h.flip.isoPullback_hom_snd
    exact he ▸ hsnd.comp h.flip.isoPullback.hom.homeomorph.isClosedMap

/-- The actual finite disjoint union is finite over its base. -/
theorem finiteConstantScheme_finite [Finite I] : IsFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
  have := finiteConstantScheme_etale S I
  have := finiteConstantScheme_affine S I
  have := finiteConstantScheme_universallyClosed S I
  have : LocallyQuasiFinite (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := by
    have := HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @LocallyQuasiFinite.{u}) (Q := @RingHom.QuasiFinite)
    change LocallyQuasiFinite (Sigma.desc (fun _ : I => 𝟙 S))
    exact IsZariskiLocalAtSource.sigmaDesc (P := @LocallyQuasiFinite.{u})
      (fun _ => inferInstanceAs (LocallyQuasiFinite (𝟙 S)))
  have : IsProper (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme S I).hom := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

variable (ℓ n : ℕ) (X : Scheme.{u})

/-- Continuous functions to discrete coefficients are exactly locally constant functions. -/
def locallyConstantContinuousEquiv {T A : Type*} [TopologicalSpace T]
    [TopologicalSpace A] [DiscreteTopology A] : LocallyConstant T A ≃ C(T, A) where
  toFun f := ⟨f, f.continuous⟩
  invFun f := ⟨f, (IsLocallyConstant.iff_continuous _).mpr f.continuous⟩
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl

/-- The finite coefficient scheme as an actual object of the pro-étale site. -/
def finiteCoefficientProEt : X.ProEt := by
  have := finiteConstantScheme_etale X (ULift.{u} (ZMod (ℓ ^ n)))
  exact Scheme.ProEt.mk (AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme X (ULift.{u} (ZMod (ℓ ^ n)))).hom

theorem finiteCoefficientProEt_finite [NeZero (ℓ ^ n)] :
    IsFinite (finiteCoefficientProEt ℓ n X).hom :=
  finiteConstantScheme_finite X (ULift.{u} (ZMod (ℓ ^ n)))

/-- Maps to the coefficient object are exactly continuous finite coefficient functions. -/
def finiteCoefficientProEtHomEquiv (U : X.ProEt) :
    (U ⟶ finiteCoefficientProEt ℓ n X) ≃ C(U.left, ZMod (ℓ ^ n)) :=
  ((Scheme.ProEt.forgetFullyFaithful X).homEquiv).trans
    ((AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantSchemePointsEquiv X (ULift.{u} (ZMod (ℓ ^ n)))
      ((Scheme.ProEt.forget X).obj U)).trans
        ((LocallyConstant.congrRight Equiv.ulift).trans
          locallyConstantContinuousEquiv))

/-- The actual coefficient sheaf is represented by the finite coefficient scheme. -/
def finiteCoefficientRepresentable :
    ((CoefficientSheaf.Construction.finiteEllAdicCoefficient ℓ n X).obj ⋙ forget Ab.{u + 1}).RepresentableBy
      (finiteCoefficientProEt ℓ n X) where
  homEquiv {U} := (finiteCoefficientProEtHomEquiv ℓ n X U).trans Equiv.ulift.symm
  homEquiv_comp f g := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    rfl

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ConstantScheme.Construction
