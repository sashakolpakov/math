import Mathlib.AlgebraicGeometry.Modules.Tilde
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Descent

/-! # Tilde Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback

noncomputable section

/-!
# Affine pullback of module sheaves for PoincareBundle

The sheaf associated to extension of scalars is identified with the
geometric pullback of the associated sheaf. The construction compares
their adjunctions; it does not assume preservation of line bundles or
effectiveness of descent.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R S : CommRingCat.{u}}

/-- Taking sections over the whole spectrum for a sheaf of R-modules. -/
def sectionsFunctor (R : CommRingCat.{u}) :
    TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
  TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)

/-- Pushforward along an affine morphism commutes with global sections,
with the corresponding restriction of scalars. -/
def pushforwardSectionsIso (f : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map f) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars f.hom := by
  let e := pushforwardCompModulesSpecToSheafIso f
  let Γ := sectionsFunctor R
  refine NatIso.ofComponents (fun N => Γ.mapIso (e.app N)) ?_
  intro M N g
  exact congrArg (fun h => Γ.map h) (e.hom.naturality g)

/-- The tilde functor commutes with arbitrary affine base change. -/
def tildePullbackIso (f : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ tilde.functor S :=
  ((tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj f.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
      (pushforwardSectionsIso f).symm)

/-- A module trivialization after localization gives an actual line-bundle
trivialization on the associated principal open subscheme. -/
def basicOpenTrivialization (M : ModuleCat.{u} R) (r : R)
    (eLocal : LocalizedModule.Away r M ≃ₗ[Localization.Away r] Localization.Away r) :
    (Scheme.Modules.pullback (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj
      (tilde M) ≅ Line.Bundles.unitLine
        (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)) := by
  let A := CommRingCat.of (Localization.Away r)
  let f : R ⟶ A := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let i := basicOpenIsoSpecAway r
  let eModule : (ModuleCat.extendScalars f.hom).obj M ≅ ModuleCat.of A A := by
    have halg : f.hom.toAlgebra = inferInstanceAs (Algebra R (Localization.Away r)) := by
      exact toAlgebra_algebraMap
    have hloc : letI := f.hom.toAlgebra
        IsLocalization (.powers r) (Localization.Away r) := by
      rw [halg]
      infer_instance
    have htower : @IsScalarTower R (Localization.Away r) (LocalizedModule.Away r M)
        f.hom.toAlgebra.toSMul inferInstance inferInstance := by
      rw [halg]
      infer_instance
    letI : Algebra R (Localization.Away r) := f.hom.toAlgebra
    haveI : IsLocalization (.powers r) (Localization.Away r) := hloc
    haveI := htower
    exact ((IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (.powers r) M)).equiv ≪≫ₗ eLocal).toModuleIso
  exact (Scheme.Modules.pullbackCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app
      (tilde M) ≪≫
    ((Scheme.Modules.pullbackComp i.hom (Spec.map f)).app (tilde M)).symm ≪≫
    (Scheme.Modules.pullback i.hom).mapIso ((tildePullbackIso f).app M) ≪≫
    (Scheme.Modules.pullback i.hom).mapIso
      ((tilde.functor A).mapIso eModule ≪≫ tildeSelf) ≪≫
    Line.Bundles.pullbackUnitIso i.hom

/-- Invertible modules give genuine algebraic line bundles on their spectra. -/
theorem isLine_tilde_of_invertible (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Line.Bundles.IsLine (tilde M) := by
  classical
  intro x
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R M
  let p : PrimeSpectrum R := x
  have hex : ∃ r ∈ s, r ∉ p.asIdeal := by
    by_contra! h
    have hle : Ideal.span (s : Set R) ≤ p.asIdeal := Ideal.span_le.mpr h
    rw [hs] at hle
    exact p.isPrime.ne_top (top_le_iff.mp hle)
  obtain ⟨r, hr, hxr⟩ := hex
  have : Module.Free (Localization.Away r) (LocalizedModule.Away r M) := hfree r hr
  obtain ⟨eLocal⟩ := (Module.Invertible.free_iff_linearEquiv
    (R := Localization.Away r) (M := LocalizedModule.Away r M)).mp inferInstance
  exact ⟨PrimeSpectrum.basicOpen r, hxr, ⟨basicOpenTrivialization M r eLocal⟩⟩

/-- The line bundle associated to an invertible module. -/
def lineBundleOfInvertible (M : ModuleCat.{u} R) [Module.Invertible R M] :
    Line.Bundles.LineBundle (Spec R) :=
  ⟨tilde M, isLine_tilde_of_invertible M⟩

/-- The algebraic line bundle obtained from affine line-module descent data. -/
def descendedLineBundle [IsNoetherianRing R] (f : R ⟶ S)
    (hf : f.hom.FaithfullyFlat) (D : Affine.Descent.ModuleDatum f.hom)
    [Module.Invertible S D.A] : Line.Bundles.LineBundle (Spec R) := by
  have := Affine.Descent.descendedModule_invertible f.hom hf D
  exact lineBundleOfInvertible (Affine.Descent.descendedModule f.hom hf D)

/-- Geometric pullback of the descended line bundle recovers the sheaf
associated with the line module on the cover. -/
def descendedLineBundlePullbackIso [IsNoetherianRing R] (f : R ⟶ S)
    (hf : f.hom.FaithfullyFlat) (D : Affine.Descent.ModuleDatum f.hom)
    [Module.Invertible S D.A] :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLineBundle f hf D).sheaf ≅
      tilde D.A :=
  (tildePullbackIso f).app (Affine.Descent.descendedModule f.hom hf D) ≪≫
    (tilde.functor S).mapIso (Affine.Descent.baseChangeIso f.hom hf D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback
