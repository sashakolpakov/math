import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalLineDescent

/-! # Faithful Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback

noncomputable section

/-!
# Faithfully flat detection of line-bundle isomorphisms for PoincareBundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Faithfully flat affine pullback detects maps of quasi-coherent sheaves
which are isomorphisms after pullback. -/
theorem spec_isIso_of_pullback {R S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.FaithfullyFlat) {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (ha : IsIso ((Scheme.Modules.pullback (Spec.map f)).map a)) : IsIso a := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let M' : Affine.QuasiCoherent.QCSheaves R := ⟨M, inferInstance⟩
  let N' : Affine.QuasiCoherent.QCSheaves R := ⟨N, inferInstance⟩
  let a' : M' ⟶ N' := ObjectProperty.homMk a
  have hp : IsIso ((Affine.QuasiCoherent.pullback f).map a') :=
    (ObjectProperty.isIso_hom_iff _).mp ha
  have := Affine.QuasiCoherent.pullback_reflectsIsomorphisms f hf
  have hi : IsIso a' := isIso_of_reflects_iso a' (Affine.QuasiCoherent.pullback f)
  exact @Functor.map_isIso _ _ _ _ _ _ P.ι a' hi

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Isomorphisms of line bundles are detected by faithfully flat pullback
between arbitrary affine schemes. -/
theorem affine_isIso_of_pullback [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    {M N : Y.Modules} (a : M ⟶ N)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (ha : IsIso ((Scheme.Modules.pullback f).map a)) : IsIso a := by
  let g := Spec.map f.appTop
  let i := X.isoSpec.symm
  let j := Y.isoSpec.symm
  let w := Scheme.isoSpec_inv_naturality f
  let α := IsoDescent.pullbackSquareIso f g i j w
  let G := Scheme.Modules.pullback j.hom
  let H := Scheme.Modules.pullback i.hom
  have hM' : (G.obj M).IsQuasicoherent :=
    QuasiCoherent.isQuasicoherent_of_isLine _ (hM.pullback j.hom)
  have hN' : (G.obj N).IsQuasicoherent :=
    QuasiCoherent.isQuasicoherent_of_isLine _ (hN.pullback j.hom)
  have hright : IsIso ((Scheme.Modules.pullback f ⋙ H).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ H ((Scheme.Modules.pullback f).map a) ha
  have hleft : IsIso ((G ⋙ Scheme.Modules.pullback g).map a) :=
    (NatIso.isIso_map_iff α a).mpr hright
  have hf : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩
  have hG : IsIso (G.map a) := spec_isIso_of_pullback f.appTop hf (G.map a) hleft
  have : G.IsEquivalence := IsoDescent.pullback_isEquivalence j
  exact isIso_of_reflects_iso a G

/-- Faithfully flat affine pullback detects isomorphisms between global
line bundles. -/
theorem isIso_of_pullback [IsAffineHom f] [Flat f] [Surjective f]
    {M N : Y.Modules} (a : M ⟶ N)
    (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
    (ha : IsIso ((Scheme.Modules.pullback f).map a)) : IsIso a := by
  apply ModuleLocality.isIso_of_locally_isIso
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
  have hM' : Line.Bundles.IsLine (G.obj M) :=
    (hM.pullback U.ι).of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
  have hN' : Line.Bundles.IsLine (G.obj N) :=
    (hN.pullback U.ι).of_iso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm
  have hleft : IsIso ((Scheme.Modules.pullback f ⋙ H).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ H ((Scheme.Modules.pullback f).map a) ha
  have hright : IsIso ((G ⋙ Scheme.Modules.pullback (f ∣_ U)).map a) :=
    (NatIso.isIso_map_iff (Open.BaseChange.pullbackRestrictIso f U) a).mp hleft
  exact ⟨U, hy, affine_isIso_of_pullback (f ∣_ U) (G.map a) hM' hN' hright⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FaithfulPullback
