import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.RestrictedAffine
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.IsoBase
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SliceEquivalence

/-! # Affine Slices -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor

noncomputable section

/-!
# Completion: actual finite étale representatives in affine slice categories

Transport from the spectrum of an affine object's coordinate ring gives
the local representatives directly over that object, ready for geometric gluing.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} (U : X.ProEt) [IsAffine U.left]

/-- The site of the affine coordinate spectrum is equivalent to the original slice. -/
def AffineSlices.Construction.proEtAffineSliceEquivalence : (Spec Γ(U.left, ⊤)).ProEt ≌ Over U :=
  (ProEtale.IsoBase.Construction.proEtIsoBaseEquivalence U.left.isoSpec.symm).trans (ProEtale.SliceEquivalence.Construction.proEtaleSliceEquivalence U)

/-- This equivalence has the original composite structure map to the base. -/
def AffineSlices.Construction.proEtAffineSliceForgetIso :
    (AffineSlices.Construction.proEtAffineSliceEquivalence U).functor ⋙ Over.forget U ≅
      ProEtale.EtaleRestriction.Construction.proEtCompose (U.left.isoSpec.inv ≫ U.hom) inferInstance :=
  NatIso.ofComponents (fun V => MorphismProperty.Over.isoMk (Iso.refl V.left)
    (by
      change (𝟙 V.left) ≫ (V.hom ≫ U.left.isoSpec.inv ≫ U.hom) =
        (V.hom ≫ U.left.isoSpec.inv) ≫ U.hom
      simp [Category.assoc]))
    (by
      intro V W g
      apply MorphismProperty.Over.Hom.ext
      change g.left ≫ 𝟙 W.left = 𝟙 V.left ≫ g.left
      simp)

variable {ℓ n : ℕ} [NeZero (ℓ ^ n)] (E : App.Construction.FiniteCoefficientExtension ℓ n X)

/-- Every affine slice of the actual torsor has an actual finite étale representative. -/
theorem App.Construction.FiniteCoefficientExtension.exists_finiteEtale_representative_affine_slice :
    ∃ T : Over U, IsFinite T.hom.left ∧ Etale T.hom.left ∧
      Nonempty (((Over.forget U).op ⋙ E.fiberPresheaf).RepresentableBy T) := by
  let b := U.left.isoSpec.inv ≫ U.hom
  have hb : WeaklyEtale b := inferInstance
  obtain ⟨T, hfin, het, ⟨rep⟩⟩ := E.exists_finiteEtale_representative_restricted_affine b hb
  let G := AffineSlices.Construction.proEtAffineSliceEquivalence U
  let e := AffineSlices.Construction.proEtAffineSliceForgetIso U
  let er : (ProEtale.EtaleRestriction.Construction.proEtCompose b hb).op ⋙ E.fiberPresheaf ≅
      G.functor.op ⋙ (Over.forget U).op ⋙ E.fiberPresheaf :=
    NatIso.ofComponents (fun V => E.fiberPresheaf.mapIso ((e.app V.unop).op))
      (by
        intro V W g
        change E.fiberPresheaf.map _ ≫ E.fiberPresheaf.map _ =
          E.fiberPresheaf.map _ ≫ E.fiberPresheaf.map _
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact E.fiberPresheaf.congr_map (congrArg Quiver.Hom.op (e.hom.naturality g.unop).symm))
  have : IsFinite T.hom := hfin
  have : Etale T.hom := het
  refine ⟨G.functor.obj T, ?_, ?_, ?_⟩
  · change IsFinite (T.hom ≫ U.left.isoSpec.inv)
    infer_instance
  · change Etale (T.hom ≫ U.left.isoSpec.inv)
    infer_instance
  · exact ⟨DenseRepresentation.Construction.representableByOfCoverDense.{u + 1, u, u + 1, u, u + 1}
      G.functor (Functor.FullyFaithful.ofFullyFaithful G.functor)
      ((Scheme.ProEt.topology X).over U) (E.fiberSheaf.over U) (rep.ofIso er)⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor
