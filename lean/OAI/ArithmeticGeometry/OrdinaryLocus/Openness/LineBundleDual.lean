import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomLocalTrivialization

/-! # Line Bundle Dual -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDual.Construction

noncomputable section

/-! Internal Homs and duals of line bundles are line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def homTrivializationAppIso {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : U.toScheme.Opens) :
    ((SheafHomModule.Construction.sheafHomModule M N).restrict U.ι).val.obj (.op V) ≅
      (LineBundle.Construction.structureSheafModule U.toScheme).val.obj (.op V) := by
  let e := HomLocalTrivialization.Construction.localHomCoordinateLinearEquiv eM eN (U.ι ''ᵁ V) (U.ι_image_le V)
  refine ModuleCat.isoMk e.toAddEquiv.toAddCommGrpIso ?_
  intro r
  ext q
  let r' : Γ(X, U.ι ''ᵁ V) := r
  let rinv : Γ(X, U.ι ''ᵁ V) := (U.ι.appIso V).inv r
  let q' : ModuleHomAdditive.Construction.moduleHomLocalAddSubgroup M N (U.ι ''ᵁ V) := q
  change r' * e q' = e (rinv • q')
  have hr : rinv = r' := by dsimp [rinv, r']; rw [Scheme.Opens.ι_appIso]; rfl
  exact (e.map_smul r' q').symm.trans (congrArg (fun a ↦ e (a • q')) hr.symm)

def homTrivializationPresheafIso {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    ((SheafHomModule.Construction.sheafHomModule M N).restrict U.ι).val ≅ (LineBundle.Construction.structureSheafModule U.toScheme).val := by
  let A : U.toScheme.PresheafOfModules := ((SheafHomModule.Construction.sheafHomModule M N).restrict U.ι).val
  let B : U.toScheme.PresheafOfModules := (LineBundle.Construction.structureSheafModule U.toScheme).val
  refine PresheafOfModules.isoMk (M₁ := A) (M₂ := B)
    (fun V ↦ homTrivializationAppIso eM eN V.unop) ?_
  intro V W h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  exact HomLocalTrivialization.Construction.localHomCoordinate_restrict eM eN (U.ι_image_le V.unop)
    (U.ι.image_mono (leOfHom h.unop)) q

def homTrivializationIso {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens}
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (SheafHomModule.Construction.sheafHomModule M N).restrict U.ι ≅ LineBundle.Construction.structureSheafModule U.toScheme :=
  (Scheme.Modules.fullyFaithfulToPresheafOfModules (X := U.toScheme)).preimageIso
    (homTrivializationPresheafIso eM eN)

theorem isLineBundle_sheafHom {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.Construction.IsLineBundle M) (hN : LineBundle.Construction.IsLineBundle N) : LineBundle.Construction.IsLineBundle (SheafHomModule.Construction.sheafHomModule M N) := by
  intro x
  obtain ⟨U, hxU, ⟨eM⟩⟩ := hM x
  obtain ⟨V, hxV, ⟨eN⟩⟩ := hN x
  let W := U ⊓ V
  let a := LineBundleQuasicoherent.Construction.lineBundleOverTrivialization W (TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_left eM)
  let b := LineBundleQuasicoherent.Construction.lineBundleOverTrivialization W (TensorRestriction.Construction.restrictLineBundleTrivialization inf_le_right eN)
  refine ⟨W, ⟨hxU, hxV⟩, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm ≪≫ homTrivializationIso a b

theorem isLineBundle_dual {X : Scheme.{u}} {M : X.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    LineBundle.Construction.IsLineBundle (SheafHomModule.Construction.lineBundleDual M) :=
  isLineBundle_sheafHom hM (LineBundle.Construction.isLineBundle_structureSheaf X)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundleDual.Construction
