import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CohomologyInduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentSupportInduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentNilpotentInduction
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CoherentClosedImageSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.ClosedSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.PushforwardCohomology

/-! # Coherent Cohomology -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoherentCohomology

noncomputable section

/-! Finiteness of actual coherent cohomology for proper schemes over a
noetherian affine base. The proof combines Chow modification, generic
comparison, and induction on closed support with actual nilpotent layers. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

theorem proper_coherent_cohomologyFinite
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : CohomologyExactFiniteness.BaseCohomologyFinite f M := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  apply CoherentSupportInduction.coherent_support_induction (CohomologyExactFiniteness.BaseCohomologyFinite f)
    (fun N hN => CohomologyExactFiniteness.BaseCohomologyFinite.of_isZero f N hN) _ M
  intro Z hZ ih N _ _ hN
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIZ : I.support = Z := SetLike.coe_injective
    (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  apply CoherentNilpotentInduction.coherent_property_of_closed_support (CohomologyExactFiniteness.BaseCohomologyFinite f) I _ N
    (hIZ.symm ▸ hN)
  intro Q _ _
  have : IsIntegral I.subscheme := Integral.ClosedSupport.vanishingIdeal_subscheme_integral Z hZ
  apply (Affine.PushforwardCohomology.baseCohomologyFinite_affinePushforward_iff I.subschemeι f Q).mpr
  apply CohomologyInduction.properIntegral_cohomologyFinite_of_proper_support (I.subschemeι ≫ f) _ Q
  intro T _ _ hT
  let P := (pushforward I.subschemeι).obj T
  have : P.IsQuasicoherent := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (M := T) I.subschemeι
  have : P.IsFiniteType := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion (M := T) I.subschemeι
  have hr : CoherentClosedImageSupport.closedImage I.subschemeι ⊤ = Z := by
    apply SetLike.coe_injective
    change I.subschemeι '' Set.univ = (Z : Set X)
    rw [Set.image_univ, Scheme.IdealSheafData.range_subschemeι]
    exact congrArg (fun W : Closeds X => (W : Set X)) hIZ
  have hP : (CoherentAnnihilator.coherentAnnihilator P).support < Z := by
    rw [← hr]
    exact lt_of_le_of_lt (CoherentClosedImageSupport.coherent_pushforward_support_le_closedImage I.subschemeι T)
      (CoherentClosedImageSupport.closedImage_lt_range_of_lt_top I.subschemeι (CoherentAnnihilator.coherentAnnihilator T).support hT)
  exact (Affine.PushforwardCohomology.baseCohomologyFinite_affinePushforward_iff I.subschemeι f T).mp (ih P hP)

theorem proper_coherent_cohomologyFinite_affine
    {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (f : X ⟶ S) [IsProper f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] : CohomologyExactFiniteness.BaseCohomologyFinite f M := by
  intro n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule (f ≫ S.toSpecΓ) M n
  let := SheafCohomology.Projective.BaseCechBridge.baseCohomologyModule f M n
  have := proper_coherent_cohomologyFinite (f ≫ S.toSpecΓ) M n
  let a : SheafCohomology.AffineH.Projective.H M n →ₛₗ[S.toSpecΓ.appTop.hom] SheafCohomology.AffineH.Projective.H M n :=
    { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective a Function.surjective_id

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Proper.CoherentCohomology
