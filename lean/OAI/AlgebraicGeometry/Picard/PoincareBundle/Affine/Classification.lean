import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuasiCoherent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.LocalInvertibility

/-! # Classification -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification

noncomputable section

/-!
# Invertible modules underlying affine line bundles for PoincareBundle

Geometric local trivializations are refined to principal opens. The affine
module equivalence turns each trivialization into a localization of rank
one, and the local invertibility criterion then applies.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : CommRingCat.{u}}

/-- Restriction of a line-bundle trivialization to a smaller open set. -/
def restrictTrivialization {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (hVU : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Line.Bundles.unitLine U) :
    (Scheme.Modules.pullback V.ι).obj M ≅ Line.Bundles.unitLine V :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE hVU)).mapIso e ≪≫
    Line.Bundles.pullbackUnitIso (X.homOfLE hVU)

/-- Comparison of categorical extension of scalars and module localization. -/
def localizationModuleIso (M : ModuleCat.{u} R) (r : R) :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj M ≅
      ModuleCat.of (Localization.Away r) (LocalizedModule.Away r M) := by
  have halg : (algebraMap R (Localization.Away r)).toAlgebra =
      inferInstanceAs (Algebra R (Localization.Away r)) := toAlgebra_algebraMap
  have hloc : letI := (algebraMap R (Localization.Away r)).toAlgebra
      IsLocalization (.powers r) (Localization.Away r) := by
    rw [halg]
    infer_instance
  have htower : @IsScalarTower R (Localization.Away r) (LocalizedModule.Away r M)
      (algebraMap R (Localization.Away r)).toAlgebra.toSMul inferInstance inferInstance := by
    rw [halg]
    infer_instance
  letI : Algebra R (Localization.Away r) := (algebraMap R (Localization.Away r)).toAlgebra
  haveI : IsLocalization (.powers r) (Localization.Away r) := hloc
  haveI := htower
  exact (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
    (LocalizedModule.mkLinearMap (.powers r) M)).equiv.toModuleIso

/-- A geometric trivialization over a principal open gives a rank-one
trivialization of the localized module. -/
def localizationEquivOfTrivialization (M : ModuleCat.{u} R) (r : R)
    (e : (Scheme.Modules.pullback
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj (tilde M) ≅
        Line.Bundles.unitLine
          (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r))) :
    LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r := by
  let A := CommRingCat.of (Localization.Away r)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let i := basicOpenIsoSpecAway r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  have hi : Spec.map f = i.inv ≫ U.ι := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap r, Iso.inv_hom_id_assoc]
  let eSheaf : tilde ((ModuleCat.extendScalars f.hom).obj M) ≅
      tilde (ModuleCat.of A A) :=
    ((TildePullback.tildePullbackIso f).app M).symm ≪≫
      (Scheme.Modules.pullbackCongr hi).app (tilde M) ≪≫
      ((Scheme.Modules.pullbackComp i.inv U.ι).app (tilde M)).symm ≪≫
      (Scheme.Modules.pullback i.inv).mapIso e ≪≫
      Line.Bundles.pullbackUnitIso i.inv ≪≫ tildeSelf.symm
  exact ((localizationModuleIso M r).symm ≪≫
    (tilde.fullyFaithfulFunctor (R := A)).preimageIso eSheaf).toLinearEquiv

/-- Each point has a principal-open neighborhood on which a line bundle
associated to a module gives a free rank-one localization. -/
theorem exists_localizationEquiv (M : ModuleCat.{u} R)
    (hM : Line.Bundles.IsLine (tilde M)) (x : PrimeSpectrum R) :
    ∃ r : R, r ∉ x.asIdeal ∧
      Nonempty (LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hM x
  obtain ⟨V, ⟨r, rfl⟩, hxr, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens hx
  exact ⟨r, hxr, ⟨localizationEquivOfTrivialization M r
    (restrictTrivialization (tilde M) hVU e)⟩⟩

/-- A module whose associated sheaf is a line bundle is invertible. -/
theorem invertible_of_isLine_tilde (M : ModuleCat.{u} R)
    (hM : Line.Bundles.IsLine (tilde M)) : Module.Invertible R M := by
  classical
  choose r hr he using exists_localizationEquiv M hM
  have hspan : Ideal.span (Set.range r) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hr x⟩
  apply LocalInvertibility.invertible_of_localizationSpan R M (Set.range r) hspan
  rintro ⟨a, x, rfl⟩
  exact Module.Invertible.congr (he x).some.symm

/-- The actual global sections of an affine geometric line bundle form
an invertible module. -/
theorem globalSections_invertible (L : Line.Bundles.LineBundle (Spec R)) :
    Module.Invertible R ((moduleSpecΓFunctor (R := R)).obj L.sheaf) :=
  invertible_of_isLine_tilde _
    (L.isLine.of_iso (QuasiCoherent.affineTildeIso L).symm)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Classification
