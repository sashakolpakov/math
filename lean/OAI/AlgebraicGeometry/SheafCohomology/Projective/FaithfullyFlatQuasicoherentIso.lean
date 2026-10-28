import OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Faithfully Flat Quasicoherent Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FaithfullyFlatQuasicoherentIso

noncomputable section

/-! Faithfully flat affine pullback detects isomorphisms of arbitrary quasicoherent modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem affine_quasicoherent_isIso_of_pullback [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (ha : IsIso ((Scheme.Modules.pullback f).map a)) : IsIso a := by
  let g := Spec.map f.appTop
  let i := X.isoSpec.symm
  let j := Y.isoSpec.symm
  let w := Scheme.isoSpec_inv_naturality f
  let α := Picard.PoincareBundle.IsoDescent.pullbackSquareIso f g i j w
  let G := Scheme.Modules.pullback j.hom
  let H := Scheme.Modules.pullback i.hom
  have : (G.obj M).IsQuasicoherent :=
    ObjectProperty.prop_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback j.hom).app M)
      (inferInstanceAs ((Scheme.Modules.restrictFunctor j.hom).obj M).IsQuasicoherent)
  have : (G.obj N).IsQuasicoherent :=
    ObjectProperty.prop_of_iso _ ((Scheme.Modules.restrictFunctorIsoPullback j.hom).app N)
      (inferInstanceAs ((Scheme.Modules.restrictFunctor j.hom).obj N).IsQuasicoherent)
  have hright : IsIso ((Scheme.Modules.pullback f ⋙ H).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ H ((Scheme.Modules.pullback f).map a) ha
  have hleft : IsIso ((G ⋙ Scheme.Modules.pullback g).map a) :=
    (NatIso.isIso_map_iff α a).mpr hright
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have : IsIso (G.map a) := Picard.PoincareBundle.FaithfulPullback.spec_isIso_of_pullback f.appTop hf (G.map a) hleft
  have : G.IsEquivalence := Picard.PoincareBundle.IsoDescent.pullback_isEquivalence j
  exact isIso_of_reflects_iso a G

theorem quasicoherent_isIso_of_faithfullyFlat_pullback [IsAffineHom f] [Flat f] [Surjective f]
    {M N : Y.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (ha : IsIso ((Scheme.Modules.pullback f).map a)) : IsIso a := by
  apply Picard.PoincareBundle.ModuleLocality.isIso_of_locally_isIso
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  have : IsAffine U := hU
  have : IsAffine (f ⁻¹ᵁ U : X.Opens) := hU.preimage f
  have : Surjective (f ∣_ U) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U).flip (inferInstanceAs (Surjective f))
  let G := Scheme.Modules.restrictFunctor U.ι
  let H := Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  have hleft : IsIso ((Scheme.Modules.pullback f ⋙ H).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ H ((Scheme.Modules.pullback f).map a) ha
  have hright : IsIso ((G ⋙ Scheme.Modules.pullback (f ∣_ U)).map a) :=
    (NatIso.isIso_map_iff (Picard.PoincareBundle.Open.BaseChange.pullbackRestrictIso f U) a).mp hleft
  exact ⟨U, hy, affine_quasicoherent_isIso_of_pullback (f ∣_ U) (G.map a) hright⟩

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FaithfullyFlatQuasicoherentIso
