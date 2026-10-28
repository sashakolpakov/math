import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Quasi Coherent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent

noncomputable section

/-!
# Affine quasi-coherent adjunctions for PoincareBundle

Pullback and direct image for an affine morphism preserve quasi-coherence.
The geometric adjunction therefore restricts to the categories equivalent
to modules over the affine coordinate rings.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- Affine pullback preserves quasi-coherent module sheaves. -/
theorem pullback_isQuasicoherent (f : R ⟶ S) (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback (Spec.map f)).obj M).IsQuasicoherent := by
  let a : tilde ((moduleSpecΓFunctor (R := R)).obj M) ⟶ M :=
    Scheme.Modules.fromTildeΓ (R := R) M
  have ha : IsIso a := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  let e := @asIso _ _ _ _ a ha
  exact (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).prop_of_iso
    (((TildePullback.tildePullbackIso f).app _).symm ≪≫
      (Scheme.Modules.pullback (Spec.map f)).mapIso e)
    (inferInstanceAs ((tilde ((ModuleCat.extendScalars f.hom).obj
      ((moduleSpecΓFunctor (R := R)).obj M))).IsQuasicoherent))

/-- Affine direct image preserves quasi-coherent module sheaves. -/
theorem pushforward_isQuasicoherent (f : R ⟶ S) (M : (Spec S).Modules)
    [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map f)).obj M).IsQuasicoherent := by
  have : IsIso (Scheme.Modules.fromTildeΓ (R := S) M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := S) M
  exact (isQuasicoherent_iff_isIso_fromTildeΓ (R := R) _).mpr
    (isIso_fromTildeΓ_pushforward f M)

/-- The category of actual quasi-coherent sheaves on an affine spectrum. -/
abbrev QCSheaves (R : CommRingCat.{u}) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory

/-- The full inclusion into all geometric module sheaves. -/
def inclusion (R : CommRingCat.{u}) : QCSheaves R ⥤ (Spec R).Modules :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι

/-- Geometric pullback restricted to quasi-coherent sheaves. -/
def pullback (f : R ⟶ S) : QCSheaves R ⥤ QCSheaves S :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf)
    (inclusion R ⋙ Scheme.Modules.pullback (Spec.map f)) (fun M => by
      have : M.obj.IsQuasicoherent := M.property
      exact pullback_isQuasicoherent f M.obj)

/-- Geometric direct image restricted to quasi-coherent sheaves. -/
def pushforward (f : R ⟶ S) : QCSheaves S ⥤ QCSheaves R :=
  ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)
    (inclusion S ⋙ Scheme.Modules.pushforward (Spec.map f)) (fun M => by
      have : M.obj.IsQuasicoherent := M.property
      exact pushforward_isQuasicoherent f M.obj)

/-- The actual geometric adjunction restricted along the full inclusions. -/
def adjunction (f : R ⟶ S) : QuasiCoherent.pullback f ⊣ QuasiCoherent.pushforward f :=
  (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- The affine module equivalence identifies geometric pullback with
extension of scalars on the quasi-coherent categories. -/
def modulePullbackIso (f : R ⟶ S) :
    (tildeEquiv (R := R)).functor ⋙ QuasiCoherent.pullback f ≅
      ModuleCat.extendScalars f.hom ⋙ (tildeEquiv (R := S)).functor := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _
    ((TildePullback.tildePullbackIso f).app M)) ?_
  intro M N a
  exact ObjectProperty.hom_ext _ ((TildePullback.tildePullbackIso f).hom.naturality a)

/-- Finite limits of affine quasi-coherent sheaves are transported from modules. -/
instance hasFiniteLimits (R : CommRingCat.{u}) : HasFiniteLimits (QCSheaves R) := by
  constructor
  intro J _ _
  exact Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse

/-- Geometric affine pullback is conjugate to extension of scalars under
the proved affine module equivalences. -/
def pullbackModuleModelIso (f : R ⟶ S) :
    QuasiCoherent.pullback f ≅ (tildeEquiv (R := R)).inverse ⋙ ModuleCat.extendScalars f.hom ⋙
      (tildeEquiv (R := S)).functor :=
  (Functor.leftUnitor (QuasiCoherent.pullback f)).symm ≪≫
    Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso.symm (QuasiCoherent.pullback f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tildeEquiv (R := R)).inverse (modulePullbackIso f)

/-- Flat affine pullback preserves finite limits of quasi-coherent sheaves. -/
theorem pullback_preservesFiniteLimits (f : R ⟶ S) (hf : f.hom.Flat) :
    PreservesFiniteLimits (QuasiCoherent.pullback f) := by
  have hExt : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have : PreservesFiniteLimits (tildeEquiv (R := R)).inverse := inferInstance
  have : PreservesFiniteLimits (tildeEquiv (R := S)).functor := inferInstance
  have : PreservesFiniteLimits (ModuleCat.extendScalars f.hom ⋙
      (tildeEquiv (R := S)).functor) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits ((tildeEquiv (R := R)).inverse ⋙
      ModuleCat.extendScalars f.hom ⋙ (tildeEquiv (R := S)).functor) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso (pullbackModuleModelIso f).symm

/-- Faithfully flat affine pullback detects isomorphisms of quasi-coherent sheaves. -/
theorem pullback_reflectsIsomorphisms (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    (QuasiCoherent.pullback f).ReflectsIsomorphisms := by
  have := ModuleCat.reflectsIsomorphisms_extendScalars_of_faithfullyFlat hf
  exact reflectsIsomorphisms_of_iso (pullbackModuleModelIso f).symm

/-- The geometric affine pullback is comonadic for a faithfully flat ring map. -/
@[instance_reducible]
def comonadicPullback (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    ComonadicLeftAdjoint (QuasiCoherent.pullback f) := by
  have := pullback_preservesFiniteLimits f hf.flat
  have := pullback_reflectsIsomorphisms f hf
  have : Comonad.HasEqualizerOfIsCosplitPair (QuasiCoherent.pullback f) := by
    constructor
    intros
    infer_instance
  have : Comonad.PreservesLimitOfIsCosplitPair (QuasiCoherent.pullback f) := by
    constructor
    intros
    infer_instance
  exact Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms (adjunction f)

/-- Effective descent for the geometric affine quasi-coherent adjunction. -/
def descentEquivalence (f : R ⟶ S) (hf : f.hom.FaithfullyFlat) :
    QCSheaves R ≌ (adjunction f).toComonad.Coalgebra := by
  have : (Comonad.comparison (adjunction f)).IsEquivalence :=
    (comonadicPullback f hf).eqv
  exact (Comonad.comparison (adjunction f)).asEquivalence

/-- The quasi-coherent sheaf constructed from geometric affine descent data. -/
def descendedSheaf (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : (adjunction f).toComonad.Coalgebra) : QCSheaves R :=
  (descentEquivalence f hf).inverse.obj D

/-- Pullback recovers the entire supplied geometric coaction. -/
def descendedDatumIso (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : (adjunction f).toComonad.Coalgebra) :
    (Comonad.comparison (adjunction f)).obj (descendedSheaf f hf D) ≅ D :=
  (descentEquivalence f hf).counitIso.app D

/-- Pullback of the descended geometric quasi-coherent sheaf is the input sheaf. -/
def descendedPullbackIso (f : R ⟶ S) (hf : f.hom.FaithfullyFlat)
    (D : (adjunction f).toComonad.Coalgebra) :
    (QuasiCoherent.pullback f).obj (descendedSheaf f hf D) ≅ D.A :=
  (Comonad.forget (adjunction f).toComonad).mapIso (descendedDatumIso f hf D)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QuasiCoherent
