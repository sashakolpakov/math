import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent

/-! # Tilde Exact -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeExact

noncomputable section

/-!
# Exactness of affine module sheaves for PoincareBundle

On principal opens, the tilde functor is module localization. These
identifications provide the local finite-limit tests needed to compare
quasi-coherent descent with invariant sheaves among all module sheaves.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {R : CommRingCat.{u}}

/-- Sections over a principal open, as an abelian group. -/
def basicSections (r : R) : (Spec R).Modules ⥤ AddCommGrpCat.{u} :=
  Scheme.Modules.toPresheaf (Spec R) ⋙
    (evaluation _ _).obj (op (PrimeSpectrum.basicOpen r))

/-- Sections of an associated sheaf on a principal open are localized modules. -/
def basicLocalizationEquiv (M : ModuleCat.{u} R) (r : R) :
    M.localizedModule (.powers r) ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).obj.obj (op (PrimeSpectrum.basicOpen r)) :=
  IsLocalizedModule.linearEquiv (.powers r) (M.localizedModuleMkLinearMap (.powers r))
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom

@[simp]
theorem basicLocalizationEquiv_mk (M : ModuleCat.{u} R) (r : R) (m : M) :
    basicLocalizationEquiv M r (M.localizedModuleMkLinearMap (.powers r) m) =
      tilde.toOpen M (PrimeSpectrum.basicOpen r) m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

/-- The localization identification is natural in the original module. -/
theorem basicLocalizationEquiv_naturality {M N : ModuleCat.{u} R} (a : M ⟶ N) (r : R) :
    (basicLocalizationEquiv N r).toLinearMap ∘ₗ
        (ModuleCat.localizedModuleMap (.powers r) a).hom.restrictScalars R =
      ((modulesSpecToSheaf.map (tilde.map a)).hom.app
          (op (PrimeSpectrum.basicOpen r))).hom ∘ₗ
        (basicLocalizationEquiv M r).toLinearMap := by
  apply IsLocalizedModule.linearMap_ext (.powers r)
    (M.localizedModuleMkLinearMap (.powers r))
    (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
  ext m
  change basicLocalizationEquiv N r
      (IsLocalizedModule.map (.powers r) (M.localizedModuleMkLinearMap (.powers r))
        (N.localizedModuleMkLinearMap (.powers r)) a.hom
          (M.localizedModuleMkLinearMap (.powers r) m)) = _
  rw [IsLocalizedModule.map_apply, basicLocalizationEquiv_mk]
  change tilde.toOpen N (PrimeSpectrum.basicOpen r) (a m) =
    ((modulesSpecToSheaf.map (tilde.map a)).hom.app (op (PrimeSpectrum.basicOpen r)))
      (basicLocalizationEquiv M r (M.localizedModuleMkLinearMap (.powers r) m))
  rw [basicLocalizationEquiv_mk]
  exact congrArg (fun b => b m) (tilde.toOpen_map_app a (PrimeSpectrum.basicOpen r)).symm

/-- The tilde functor evaluated on a principal open agrees naturally
with the exact module localization functor. -/
def localizationSectionsIso (r : R) :
    ModuleCat.localizedModuleFunctor (.powers r) ⋙
        forget₂ (ModuleCat (Localization.Away r)) AddCommGrpCat.{u} ≅
      tilde.functor R ⋙ basicSections r := by
  refine NatIso.ofComponents (fun M =>
    (basicLocalizationEquiv M r).toAddEquiv.toAddCommGrpIso) ?_
  intro M N a
  ext m
  exact LinearMap.congr_fun (basicLocalizationEquiv_naturality a r) m

/-- Evaluation on a principal open preserves limits of module sheaves. -/
instance basicSections_preservesFiniteLimits (r : R) :
    PreservesFiniteLimits (basicSections r) := by
  have : PreservesFiniteLimits
      ((evaluation (TopologicalSpace.Opens (Spec R))ᵒᵖ AddCommGrpCat.{u}).obj
        (op (PrimeSpectrum.basicOpen r))) := ⟨fun _ _ _ => inferInstance⟩
  exact comp_preservesFiniteLimits _ _

/-- Associated sheaves preserve finite limits after evaluation on a principal open. -/
theorem tilde_basicSections_preservesFiniteLimits (r : R) :
    PreservesFiniteLimits (tilde.functor R ⋙ basicSections r) := by
  have : PreservesFiniteLimits (ModuleCat.localizedModuleFunctor (.powers r) ⋙
      forget₂ (ModuleCat (Localization.Away r)) AddCommGrpCat.{u}) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (localizationSectionsIso r)

/-- Principal-open sections jointly detect isomorphisms of module sheaves. -/
theorem isIso_of_basicSections {M N : (Spec R).Modules} (a : M ⟶ N)
    (h : ∀ r : R, IsIso ((basicSections r).map a)) : IsIso a := by
  let b : (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (Spec R)) ⟶
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} (Spec R)) :=
    ⟨a.mapPresheaf⟩
  have hb : IsIso b := TopCat.Sheaf.isIso_iff_isIso_basis
    PrimeSpectrum.isBasis_basic_opens h
  have : IsIso ((Scheme.Modules.toPresheaf (Spec R)).map a) :=
    @Functor.map_isIso _ _ _ _ _ _ (TopCat.Sheaf.forget AddCommGrpCat.{u} (Spec R)) b hb
  exact isIso_of_reflects_iso a (Scheme.Modules.toPresheaf (Spec R))

/-- The sheaf associated to a module preserves finite limits. -/
theorem tilde_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) := by
  constructor
  intro J _ _
  constructor
  intro K
  have hiso : IsIso (limit.post K (tilde.functor R)) := by
    apply isIso_of_basicSections
    intro r
    have := tilde_basicSections_preservesFiniteLimits r
    have hcomp : IsIso ((basicSections r).map (limit.post K (tilde.functor R)) ≫
        limit.post (K ⋙ tilde.functor R) (basicSections r)) := by
      rw [limit.post_post]
      infer_instance
    exact (isIso_comp_right_iff _
      (limit.post (K ⋙ tilde.functor R) (basicSections r))).mp hcomp
  exact preservesLimit_of_isIso_post (tilde.functor R) K

/-- The inclusion of affine quasi-coherent sheaves is an exact functor. -/
theorem inclusion_preservesFiniteLimits :
    PreservesFiniteLimits (Affine.QuasiCoherent.inclusion R) := by
  have := tilde_preservesFiniteLimits (R := R)
  have : PreservesFiniteLimits ((tildeEquiv (R := R)).inverse ⋙ tilde.functor R) :=
    comp_preservesFiniteLimits _ _
  let e0 : tilde.functor R ≅ (tildeEquiv (R := R)).functor ⋙
      Affine.QuasiCoherent.inclusion R := Iso.refl _
  let e : (tildeEquiv (R := R)).inverse ⋙ tilde.functor R ≅
      Affine.QuasiCoherent.inclusion R :=
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse e0 ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso
        (Affine.QuasiCoherent.inclusion R) ≪≫ Functor.leftUnitor _
  exact preservesFiniteLimits_of_natIso e

/-- Flat geometric pullback preserves finite diagrams of quasi-coherent sheaves,
with the limits computed among all module sheaves. -/
theorem pullback_preserves_qc_diagram {S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.Flat) {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Affine.QuasiCoherent.QCSheaves R) :
    PreservesLimit (K ⋙ Affine.QuasiCoherent.inclusion R)
      (Scheme.Modules.pullback (Spec.map f)) := by
  have := inclusion_preservesFiniteLimits (R := R)
  have := inclusion_preservesFiniteLimits (R := S)
  have := Affine.QuasiCoherent.pullback_preservesFiniteLimits f hf
  have : PreservesFiniteLimits (Affine.QuasiCoherent.pullback f ⋙
      Affine.QuasiCoherent.inclusion S) := comp_preservesFiniteLimits _ _
  exact preservesLimit_of_preserves_limit_cone
    (isLimitOfPreserves (Affine.QuasiCoherent.inclusion R) (limit.isLimit K))
    (isLimitOfPreserves (Affine.QuasiCoherent.pullback f ⋙
      Affine.QuasiCoherent.inclusion S) (limit.isLimit K))

/-- A finite diagram of quasi-coherent sheaves has its raw limit preserved
by flat affine pullback. -/
theorem pullback_preserves_diagram {S : CommRingCat.{u}} (f : R ⟶ S)
    (hf : f.hom.Flat) {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ (Spec R).Modules) (hK : ∀ j, (K.obj j).IsQuasicoherent) :
    PreservesLimit K (Scheme.Modules.pullback (Spec.map f)) := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let K' := P.lift K hK
  have hp : PreservesLimit (P.lift K hK ⋙ P.ι)
      (Scheme.Modules.pullback (Spec.map f)) := pullback_preserves_qc_diagram f hf K'
  exact (preservesLimit_iff_of_iso_diagram (Scheme.Modules.pullback (Spec.map f))
    (P.liftCompιIso K hK)).mp hp

/-- The raw equalizer of maps of quasi-coherent sheaves remains quasi-coherent. -/
theorem limit_isQuasicoherent {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ (Spec R).Modules) (hK : ∀ j, (K.obj j).IsQuasicoherent) :
    (limit K).IsQuasicoherent := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let K' := P.lift K hK
  have := inclusion_preservesFiniteLimits (R := R)
  let e : (Affine.QuasiCoherent.inclusion R).obj (limit K') ≅ limit K :=
    preservesLimitIso (Affine.QuasiCoherent.inclusion R) K' ≪≫
      HasLimit.isoOfNatIso (P.liftCompιIso K hK)
  exact P.prop_of_iso e (limit K').property

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeExact
